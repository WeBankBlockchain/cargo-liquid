// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    utils,
    workspace::{ManifestPath, Workspace},
    Verbosity,
};
use anyhow::{Context, Result};
use colored::Colorize;
use console::Emoji;
use crossterm::{
    cursor::{self, DisableBlinking, EnableBlinking, MoveTo},
    execute, terminal,
};
use indicatif::HumanDuration;
use parity_wasm::elements::{Module, Section};
use std::sync::mpsc::channel;
use std::{
    io::{self, stderr, Write},
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
    thread,
    time::{Duration, Instant},
};

struct CrateMetadata {
    manifest_path: ManifestPath,
    cargo_meta: cargo_metadata::Metadata,
    package_name: String,
    root_package: cargo_metadata::Package,
    original_wasm: PathBuf,
    dest_wasm: PathBuf,
    dest_abi: PathBuf,
}

impl CrateMetadata {
    pub fn target_dir(&self) -> &Path {
        self.cargo_meta.target_directory.as_path()
    }
}

/// Parses the manifest and returns relevant metadata.
fn collect_crate_metadata(manifest_path: &ManifestPath) -> Result<CrateMetadata> {
    let (metadata, root_package_id) = utils::get_cargo_metadata(manifest_path)?;

    // Find the root package by id in the list of packages. It is logical error if the root
    // package is not found in the list.
    let root_package = metadata
        .packages
        .iter()
        .find(|package| package.id == root_package_id)
        .expect("The package is not in the `cargo metadata` output")
        .clone();
    // Normalize the package name.
    let package_name = root_package.name.replace("-", "_");

    let mut original_wasm = metadata.target_directory.clone();
    original_wasm.push("wasm32-unknown-unknown");
    original_wasm.push("release");
    original_wasm.push(package_name.clone());
    original_wasm.set_extension("wasm");

    let mut dest_wasm = metadata.target_directory.clone();
    dest_wasm.push(package_name.clone());
    dest_wasm.set_extension("wasm");

    let mut dest_abi = metadata.target_directory.clone();
    dest_abi.push(package_name.clone());
    dest_abi.set_extension("abi");

    let crate_metadata = CrateMetadata {
        manifest_path: manifest_path.clone(),
        cargo_meta: metadata,
        root_package,
        package_name,
        original_wasm,
        dest_wasm,
        dest_abi,
    };

    Ok(crate_metadata)
}

fn build_cargo_project(
    crate_metadata: &CrateMetadata,
    use_gm: bool,
    verbosity: Verbosity,
) -> Result<()> {
    utils::check_channel()?;
    std::env::set_var(
        "RUSTFLAGS",
        "--emit mir -C link-arg=-z -C link-arg=stack-size=65536",
    );

    let verbosity = Some(match verbosity {
        Verbosity::Verbose => xargo_lib::Verbosity::Verbose,
        Verbosity::Quiet => xargo_lib::Verbosity::Quiet,
    });

    let xbuild = |manifest_path: &ManifestPath| {
        let manifest_path = Some(manifest_path);
        let target = Some("wasm32-unknown-unknown");
        let target_dir = crate_metadata.target_dir();
        let target_dir_args = &format!("--target-dir={}", target_dir.to_string_lossy());

        let mut other_args = ["--no-default-features", "--release", target_dir_args].to_vec();
        if use_gm {
            other_args.push("--features=gm");
        }

        let args = xargo_lib::Args::new(target, manifest_path, verbosity, &other_args)
            .map_err(|e| anyhow::anyhow!("{}", e))
            .context("Creating xargo args")?;

        let config = xargo_lib::Config {
            sysroot_path: target_dir.join("sysroot"),
            memcpy: false,
            panic_immediate_abort: true,
        };

        let exit_status = xargo_lib::build(args, "build", Some(config))
            .map_err(|e| anyhow::anyhow!("{}", e))
            .context("Building with xbuild")?;
        if !exit_status.success() {
            anyhow::bail!("xbuild failed with status {}", exit_status)
        }
        Ok(())
    };

    Workspace::new(&crate_metadata.cargo_meta, &crate_metadata.root_package.id)?
        .with_root_package_manifest(|manifest| {
            manifest
                .with_removed_crate_type("rlib")?
                .with_profile_release_lto(true)?;
            Ok(())
        })?
        .using_temp(xbuild)?;

    Ok(())
}

/// Strips all custom sections.
///
/// Presently all custom sections are not required so they can be stripped safely.
fn strip_custom_sections(module: &mut Module) {
    module.sections_mut().retain(|section| {
        !matches!(
            section,
            Section::Custom(_) | Section::Name(_) | Section::Reloc(_)
        )
    });
}

/// Attempts to perform optional wasm optimization using `wasm-opt`.
///
/// The intention is to reduce the size of bloated wasm binaries as a result of missing
/// optimizations (or bugs?) between Rust and Wasm.
///
/// This step depends on the `wasm-opt` tool being installed. If it is not the build will still
/// succeed, and the user will be encouraged to install it for further optimizations.
fn optimize_wasm(crate_metadata: &CrateMetadata) -> Result<()> {
    // Deserialize wasm module from a file.
    let mut module =
        parity_wasm::deserialize_file(&crate_metadata.original_wasm).context(format!(
            "Loading original wasm file '{}'",
            crate_metadata.original_wasm.display()
        ))?;

    // Perform optimization.
    //
    // In practice only tree-shaking is performed, i.e transitively removing all symbols that are
    // NOT used by the specified entrypoints.
    if pwasm_utils::optimize(
        &mut module,
        ["main", "deploy", "memory", "hash_type"].to_vec(),
    )
    .is_err()
    {
        anyhow::bail!("Optimizer failed");
    }
    strip_custom_sections(&mut module);

    parity_wasm::serialize_to_file(&crate_metadata.dest_wasm, module)?;

    // check `wasm-opt` installed
    if which::which("wasm-opt").is_err() {
        eprintln!(
            "{}",
            "wasm-opt is not installed. Install this tool on your system in order to \n\
             reduce the size of your Wasm binary. \n\
             See https://github.com/WebAssembly/binaryen#tools"
                .bright_yellow()
        );
        return Ok(());
    }

    let mut optimized = crate_metadata.dest_wasm.clone();
    optimized.set_file_name(format!("{}-opt.wasm", crate_metadata.package_name));

    let output = Command::new("wasm-opt")
        .arg(crate_metadata.dest_wasm.as_os_str())
        .arg("-g")
        .arg("-O3") // execute -O3 optimization passes (spends potentially a lot of time optimizing)
        .arg("-o")
        .arg(optimized.as_os_str())
        .output()?;

    if !output.status.success() {
        // Dump the output streams produced by wasm-opt into the stdout/stderr.
        io::stdout().write_all(&output.stdout)?;
        io::stderr().write_all(&output.stderr)?;
        anyhow::bail!("wasm-opt optimization failed");
    }

    // overwrite existing destination wasm file with the optimised version
    std::fs::rename(&optimized, &crate_metadata.dest_wasm)?;
    Ok(())
}

fn generate_abi(crate_meta: &CrateMetadata, verbosity: Verbosity) -> Result<()> {
    utils::check_channel()?;
    std::env::set_var("RUSTFLAGS", "");

    let build = |manifest_path: &ManifestPath| -> Result<()> {
        let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
        let mut cmd = Command::new(cargo);

        let origin_manifest_path = crate_meta.manifest_path.as_ref().canonicalize()?;
        let work_dir = origin_manifest_path
            .parent()
            .expect("The manifest path is a file path so has a parent");
        cmd.current_dir(work_dir);

        [
            "run",
            "--package",
            "abi-gen",
            format!(
                "--manifest-path={}",
                manifest_path.as_ref().to_string_lossy()
            )
            .as_str(),
            format!("--target-dir={}", crate_meta.target_dir().to_string_lossy()).as_str(),
            match verbosity {
                Verbosity::Quiet => "--quiet",
                Verbosity::Verbose => "--verbose",
            },
        ]
        .iter()
        .for_each(|arg| {
            cmd.arg(arg);
        });

        let status = cmd
            .status()
            .context(format!("Error executing `{:?}`", cmd))?;
        if status.success() {
            Ok(())
        } else {
            anyhow::bail!("`{:?}` failed with exit code: {:?}", cmd, status.code())
        }
    };

    Workspace::new(&crate_meta.cargo_meta, &crate_meta.root_package.id)?
        .with_root_package_manifest(|manifest| {
            manifest
                .with_added_crate_type("rlib")?
                .with_profile_release_lto(true)?;
            Ok(())
        })?
        .using_temp(build)?;

    Ok(())
}

static LOOKING_GLASS: Emoji<'_, '_> = Emoji("🔍 ", "d(・ω・d)");
static TRUCK: Emoji<'_, '_> = Emoji("🚚 ", "(∫・ω・)∫");
static CLIP: Emoji<'_, '_> = Emoji("🔗 ", "∇(・ω・∇)");
static PAPER: Emoji<'_, '_> = Emoji("📃 ", "∂(・ω・∂)");
static SPARKLE: Emoji<'_, '_> = Emoji("✨ ", "(˘•ω•˘)ง ");

struct FormattedDuration(Duration);

impl std::fmt::Display for FormattedDuration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut t = self.0.as_millis();
        let millis = t % 1000;
        t /= 1000;
        let seconds = t % 60;
        t /= 60;
        let minutes = t % 60;
        t /= 60;
        let hours = t % 24;
        t /= 24;
        if t > 0 {
            let days = t;
            write!(
                f,
                "{}d {:02}:{:02}:{:02}.{:03}",
                days, hours, minutes, seconds, millis
            )
        } else {
            write!(
                f,
                "{:02}:{:02}:{:02}.{:03}",
                hours, minutes, seconds, millis
            )
        }
    }
}

fn execute_task<F, T, E>(
    stage: &str,
    emoji: Emoji<'_, '_>,
    message: &str,
    f: F,
    show_animation: bool,
) -> Result<T, E>
where
    F: FnOnce() -> Result<T, E> + Send + 'static,
    T: Send + 'static,
    E: Send + 'static,
{
    const INDICATES: [char; 4] = ['|', '/', '-', '\\'];
    let stage = stage.bold().dimmed();
    let message = message.bold().bright_green();
    let started = Instant::now();

    if show_animation {
        let origin_pos = cursor::position().unwrap();
        eprintln!();

        let (tx, rx) = channel();
        let t = thread::spawn(move || {
            let result = f();
            tx.send(matches!(result, Ok(_))).unwrap();
            result
        });

        let mut i = 0;
        let mut stderr = stderr();
        let success = loop {
            if let Ok(success) = rx.try_recv() {
                break success;
            }

            let elapsed = format!("[{}]", FormattedDuration(started.elapsed())).cyan();
            let info = format!(
                "{} {} {} {: <25} {}\r",
                INDICATES[i], stage, emoji, message, elapsed
            );
            i = (i + 1) % INDICATES.len();

            {
                let mut handle = stderr.lock();
                let cursor_pos = cursor::position().unwrap();
                if cursor_pos.1 - origin_pos.1 > 8 {
                    break false;
                }

                execute!(handle, DisableBlinking, MoveTo(origin_pos.0, origin_pos.1)).unwrap();
                handle.write_all(info.as_bytes()).unwrap();
                handle.flush().unwrap();
                execute!(handle, EnableBlinking, MoveTo(cursor_pos.0, cursor_pos.1),).unwrap();
            }

            thread::sleep(Duration::from_millis(50));
        };

        if success {
            let elapsed = format!("[{}]", FormattedDuration(started.elapsed())).cyan();
            let info = format!(
                "{} {} {} {: <25} {}\n",
                "√".green(),
                stage,
                emoji,
                message,
                elapsed,
            );
            let cursor_pos = cursor::position().unwrap();
            execute!(stderr, MoveTo(origin_pos.0, origin_pos.1)).unwrap();
            stderr.write_all(info.as_bytes()).unwrap();
            execute!(stderr, MoveTo(cursor_pos.0, cursor_pos.1)).unwrap();
        }
        t.join().unwrap()
    } else {
        eprintln!("{}", format!("* {} {} {}", stage, emoji, message));
        f()
    }
}

pub(crate) fn execute_build(
    manifest_path: ManifestPath,
    use_gm: bool,
    verbosity: Verbosity,
) -> Result<String> {
    let started = Instant::now();
    let terminal_size = terminal::size();
    let current_pos = cursor::position();
    let show_animation = matches!(verbosity, Verbosity::Quiet)
        && match (terminal_size, current_pos) {
            (Ok(terminal_size), Ok(current_pos)) => {
                !(terminal_size.1 < 16 || terminal_size.1 - current_pos.1 < 16)
            }
            _ => false,
        };
    let crate_metadata;

    {
        let result = execute_task(
            "[1/4]",
            LOOKING_GLASS,
            "Collecting crate metadata",
            move || collect_crate_metadata(&manifest_path),
            show_animation,
        );
        crate_metadata = Arc::new(result?);
    }

    {
        let crate_metadata = crate_metadata.clone();
        execute_task(
            "[2/4]",
            TRUCK,
            "Building cargo project",
            move || build_cargo_project(crate_metadata.as_ref(), use_gm, verbosity),
            show_animation,
        )?;
    }

    {
        let crate_metadata = crate_metadata.clone();
        execute_task(
            "[3/4]",
            CLIP,
            "Optimizing Wasm bytecode",
            move || optimize_wasm(crate_metadata.as_ref()),
            show_animation,
        )?;
    }

    {
        let crate_metadata = crate_metadata.clone();
        execute_task(
            "[4/4]",
            PAPER,
            "Generating ABI file",
            move || generate_abi(crate_metadata.as_ref(), verbosity),
            show_animation,
        )?;
    }

    Ok(format!(
        "\n{}Done in {}, your project is ready now:\n{: >6}: {}\n{: >6}: {}",
        SPARKLE,
        HumanDuration(started.elapsed()),
        "Binary".green().bold(),
        crate_metadata.dest_wasm.display().to_string().bold(),
        "ABI".green().bold(),
        crate_metadata.dest_abi.display().to_string().bold(),
    ))
}
