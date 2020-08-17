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
use parity_wasm::elements::{Module, Section};
use std::{
    io::{self, Write},
    path::{Path, PathBuf},
    process::Command,
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

/// Parses the contract manifest and returns relevant metadata.
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
    verbosity: &Option<Verbosity>,
) -> Result<()> {
    utils::check_channel()?;
    std::env::set_var("RUSTFLAGS", "-C link-arg=-z -C link-arg=stack-size=65536");

    let verbosity = Some(match verbosity {
        Some(Verbosity::Verbose) => xargo_lib::Verbosity::Verbose,
        Some(Verbosity::Quiet) | None => xargo_lib::Verbosity::Quiet,
    });

    let xbuild = |manifest_path: &ManifestPath| {
        let manifest_path = Some(manifest_path);
        let target = Some("wasm32-unknown-unknown");
        let target_dir = crate_metadata.target_dir();
        let other_args = [
            "--no-default-features",
            "--release",
            &format!("--target-dir={}", target_dir.to_string_lossy()),
        ];
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
    module.sections_mut().retain(|section| match section {
        Section::Custom(_) => false,
        Section::Name(_) => false,
        Section::Reloc(_) => false,
        _ => true,
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
    if pwasm_utils::optimize(&mut module, ["call", "deploy"].to_vec()).is_err() {
        anyhow::bail!("Optimizer failed");
    }
    strip_custom_sections(&mut module);

    parity_wasm::serialize_to_file(&crate_metadata.dest_wasm, module)?;

    // check `wasm-opt` installed
    if which::which("wasm-opt").is_err() {
        println!(
            "{}",
            "wasm-opt is not installed. Install this tool on your system in order to \n\
             reduce the size of your contract's Wasm binary. \n\
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

fn generate_abi(crate_meta: &CrateMetadata, verbosity: &Option<Verbosity>) -> Result<()> {
    utils::check_channel()?;
    std::env::set_var("RUSTFLAGS", "");

    let build = |manifest_path: &ManifestPath| -> Result<()> {
        let cargo = std::env::var("CARGO").unwrap_or("cargo".to_string());
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
                Some(Verbosity::Quiet) | None => "--quiet",
                Some(Verbosity::Verbose) => "--verbose",
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

pub(crate) fn execute_build(
    manifest_path: ManifestPath,
    verbosity: Option<Verbosity>,
) -> Result<String> {
    println!(
        "{} {}",
        "[1/4]".bold(),
        "Collection crate metadata".bright_green().bold()
    );
    let crate_metadata = collect_crate_metadata(&manifest_path)?;

    println!(
        "{} {}",
        "[2/4]".bold(),
        "Building cargo project".bright_green().bold()
    );
    build_cargo_project(&crate_metadata, &verbosity)?;

    println!(
        "{} {}",
        "[3/4]".bold(),
        "Optimizing wasm file".bright_green().bold()
    );
    optimize_wasm(&crate_metadata)?;

    println!(
        "{} {}",
        "[4/4]".bold(),
        "Generating ABI file".bright_green().bold()
    );
    generate_abi(&crate_metadata, &verbosity)?;

    Ok(format!(
        "Your contract is ready:\n  binary: {}\n  ABI : {}",
        crate_metadata.dest_wasm.display().to_string().bold(),
        crate_metadata.dest_abi.display().to_string().bold(),
    ))
}
