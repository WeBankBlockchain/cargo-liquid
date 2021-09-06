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
    AnalysisBehavior, VerbosityBehavior,
};
use anyhow::{Context, Result};
use colored::Colorize;
use console::Emoji;
use indicatif::HumanDuration;
use itertools::Itertools;
use parity_wasm::elements::{Module, Section};
use serde_json::{Map, Value};
use std::{
    collections::HashMap,
    env, fs,
    io::{self, Write},
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};
use tiny_keccak::Hasher;

struct CrateMetadata {
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

const BUILD_TARGET_ARCH: &str = "wasm32-unknown-unknown";

/// Parses the manifest and returns relevant metadata.
fn collect_crate_metadata(manifest_path: &ManifestPath) -> Result<CrateMetadata> {
    let (metadata, root_package_id) = utils::get_cargo_metadata(manifest_path)?;

    // Find the root package by id in the list of packages. It is logical error if the root
    // package is not found in the list.
    let root_package = metadata
        .packages
        .iter()
        .find(|package| package.id == root_package_id)
        .expect("the package is not in the `cargo metadata` output")
        .clone();
    // Normalize the package name.
    let package_name = root_package.name.replace("-", "_");

    let mut original_wasm = metadata.target_directory.clone();
    original_wasm.push(BUILD_TARGET_ARCH);
    original_wasm.push("release");
    original_wasm.push("deps");
    original_wasm.push(package_name.clone());
    original_wasm.set_extension("wasm");

    let mut dest_wasm = metadata.target_directory.clone();
    dest_wasm.push(package_name.clone());
    dest_wasm.set_extension("wasm");

    let mut dest_abi = dest_wasm.clone();
    dest_abi.set_extension("abi");

    let crate_metadata = CrateMetadata {
        cargo_meta: metadata,
        root_package,
        package_name,
        original_wasm,
        dest_wasm,
        dest_abi,
    };

    Ok(crate_metadata)
}

fn run_xargo_build(
    crate_metadata: &CrateMetadata,
    use_gm: bool,
    verbosity_behavior: VerbosityBehavior,
    skip_analysis: bool,
) -> Result<String> {
    utils::check_channel()?;

    let xbuild = |manifest_path: &ManifestPath| {
        let manifest_dir = manifest_path.as_ref().parent().unwrap();
        if !skip_analysis {
            env::set_var("LIQUID_ANALYSIS_TARGET_DIR", manifest_dir);
        }

        let manifest_path = Some(manifest_path);
        let target = Some(BUILD_TARGET_ARCH);
        let target_dir = crate_metadata.target_dir();
        let target_dir_arg = format!("--target-dir={}", target_dir.to_string_lossy());
        let mut other_args = ["--no-default-features", "--release", &target_dir_arg].to_vec();
        if use_gm {
            other_args.push("--features=gm");
        }

        let args = xargo_lib::Args::new(
            target,
            manifest_path,
            Some(verbosity_behavior.into()),
            other_args,
        )
        .map_err(|e| anyhow::anyhow!("{}", e))
        .context("Creating xargo args")?;
        let config = xargo_lib::Config {
            sysroot_path: target_dir.join("sysroot"),
            memcpy: false,
            panic_immediate_abort: true,
        };
        let exit_status = xargo_lib::build(args, "build", Some(config))
            .map_err(|e| anyhow::anyhow!("{}", e))
            .context("Building with xargo")?;
        if !exit_status.success() {
            anyhow::bail!("xbuild failed with status {}", exit_status);
        }

        if !skip_analysis {
            fs::read_to_string(manifest_dir.join("conflict_fields.analysis")).map_err(|e| {
                anyhow::anyhow!(
                    "unable to read results file of conflict fields analysis due to: {}",
                    e
                )
            })
        } else {
            Ok(String::new())
        }
    };

    Workspace::new(&crate_metadata.cargo_meta, &crate_metadata.root_package.id)?
        .with_root_package_manifest(|manifest| {
            manifest
                .with_removed_crate_type("rlib")?
                .with_profile_release_lto(true)?;
            Ok(())
        })?
        .using_temp(xbuild)
}

fn build_cargo_project(
    crate_metadata: &CrateMetadata,
    use_gm: bool,
    verbosity_behavior: VerbosityBehavior,
    analysis_behavior: AnalysisBehavior,
    cfg_path: &Option<PathBuf>,
) -> Result<String> {
    const RUSTFLAGS_ENV_VAR: &str = "RUSTFLAGS";
    const RUSTC_WRAPPER_ENV_VAR: &str = "RUSTC_WRAPPER";

    let old_flags = env::var(RUSTFLAGS_ENV_VAR);
    if let Ok(ref old_flags) = old_flags {
        env::set_var(
            RUSTFLAGS_ENV_VAR,
            [old_flags, "-C link-arg=-z -C link-arg=stack-size=65536"].join(" "),
        );
    }

    if analysis_behavior == AnalysisBehavior::Enforce {
        // This is a dirty way to enforce starting liquid-analy, just make cargo to
        // think that the target directory is dirty now. 🙈
        drop(fs::remove_file(&crate_metadata.original_wasm));
    }

    let mut old_wrapper = Err(env::VarError::NotPresent);
    let skip_analysis = if analysis_behavior != AnalysisBehavior::Skip {
        // Sets `RUSTC_WRAPPER` environment variable for current process, which leads
        // cargo to invoke liquid-analy as compiler, and liquid-analy can then obtain
        // full list of command line arguments of the invocation above.
        //
        // ## Why not use `RUSTC`?
        // Due to that we use unstable version of rustc, and features supported by
        // the compiler is inconstant, using compilers of different version to test
        // this project is significant. Via setting different `RUSTC` value we can
        // achieve this aim easily. But if we use `RUSTC` directly here, then it
        // becomes difficult to decide which version of rustc to use in liquid-analy.
        old_wrapper = env::var(RUSTC_WRAPPER_ENV_VAR);
        env::set_var(RUSTC_WRAPPER_ENV_VAR, "liquid-analy");

        // The `LIQUID_ANALYSIS_PROJECT` environment variable is used to tell
        // liquid-analy the project it needs to care about.
        env::set_var(
            "LIQUID_ANALYSIS_PROJECT",
            crate_metadata.package_name.clone(),
        );

        if let Some(cfg_path) = cfg_path {
            let abs_path = if cfg_path.is_absolute() {
                cfg_path.to_path_buf()
            } else {
                let cur_dir = env::current_dir()?;
                cur_dir.join(cfg_path)
            };
            env::set_var("LIQUID_ANALYSIS_CFG_PATH", abs_path);
        }
        false
    } else {
        true
    };

    let build_result = run_xargo_build(crate_metadata, use_gm, verbosity_behavior, skip_analysis);

    if analysis_behavior != AnalysisBehavior::Skip {
        env::set_var(
            RUSTFLAGS_ENV_VAR,
            if let Ok(old_flags) = old_flags {
                old_flags
            } else {
                "".into()
            },
        );
        env::set_var(
            RUSTC_WRAPPER_ENV_VAR,
            if let Ok(old_wrapper) = old_wrapper {
                old_wrapper
            } else {
                "".into()
            },
        );
    }

    build_result
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

    // overwrite existing destination wasm file with the optimized version
    fs::rename(&optimized, &crate_metadata.dest_wasm)?;
    Ok(())
}

fn parse_ty(ty_info: &Map<String, Value>) -> String {
    const TUPLE_TY: &str = "tuple";

    let ty = ty_info.get("type").unwrap().as_str().unwrap();
    if ty.starts_with(TUPLE_TY) {
        let components = ty_info.get("components").unwrap().as_array().unwrap();
        let component_types = components
            .iter()
            .map(|component| parse_ty(component.as_object().unwrap()))
            .join(",");
        format!("({}){}", component_types, &ty[TUPLE_TY.len()..])
    } else {
        String::from(ty)
    }
}

fn calc_selector(source: &[u8]) -> String {
    let mut hasher_buffer = [0u8; 32];
    // The length of LEB128-encoded a 32-bit unsigned integer is at most 5.
    let mut leb128_buffer = [0u8; 5];

    let mut keccak_hasher = tiny_keccak::Keccak::v256();
    keccak_hasher.update(source);
    keccak_hasher.finalize(&mut hasher_buffer);

    let selector = u32::from_le_bytes([
        hasher_buffer[0],
        hasher_buffer[1],
        hasher_buffer[2],
        hasher_buffer[3],
    ]);

    let size = {
        let mut writer = &mut leb128_buffer[..];
        leb128::write::signed(&mut writer, (selector as i32) as i64).unwrap()
    };

    unsafe { String::from_utf8_unchecked(leb128_buffer[..size].to_vec()) }
}

fn generate_abi(crate_meta: &CrateMetadata, verbosity_behavior: VerbosityBehavior) -> Result<()> {
    utils::check_channel()?;

    let build = |manifest_path: &ManifestPath| -> Result<()> {
        let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
        let mut cmd = Command::new(cargo);

        let work_dir = crate_meta
            .dest_abi
            .parent()
            .expect("the ABI file is a file path so has a parent");
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
            match verbosity_behavior {
                VerbosityBehavior::Quiet => "--quiet",
                VerbosityBehavior::Verbose => "--verbose",
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
            let dest_wasm = &crate_meta.dest_wasm;
            let mut wasm_content =
                unsafe { String::from_utf8_unchecked(fs::read(dest_wasm).unwrap()) };

            let dest_abi = &crate_meta.dest_abi;
            let abi_content = fs::read_to_string(dest_abi)?;
            let abi: Map<String, Value> = serde_json::from_str(&abi_content)?;

            let mut sel_replacements = HashMap::new();
            for (_, fns) in &abi {
                let fns = fns.as_array().unwrap();
                for f in fns {
                    let fn_info = f.as_object().unwrap();
                    let ty = fn_info.get("type").unwrap().as_str().unwrap();
                    if ty == "function" {
                        let fn_name = fn_info.get("name").unwrap().as_str().unwrap();
                        let inputs = fn_info.get("inputs").unwrap().as_array().unwrap();
                        let sig = inputs
                            .iter()
                            .map(|input| parse_ty(input.as_object().unwrap()))
                            .join(",");
                        let sig = format!("{}({})", fn_name, sig);

                        let old_sel = calc_selector(fn_name.as_bytes());
                        let new_sel = calc_selector(sig.as_bytes());
                        let entry = sel_replacements.entry(old_sel).or_insert((
                            0,
                            new_sel.clone(),
                            String::from(fn_name),
                        ));
                        if entry.0 != 0 && entry.1 != new_sel {
                            anyhow::bail!("method `{}` cannot be invoked correctly, please rename this method or modify its signature", fn_name)
                        }
                        entry.0 += 1;
                    }
                }
            }

            for (old_sel, (count, new_sel, fn_name)) in sel_replacements {
                let match_indices = wasm_content.match_indices(&old_sel).collect::<Vec<_>>();

                if match_indices.len() != count {
                    anyhow::bail!("method `{}` cannot be invoked correctly, please rename this method or modify its signature", fn_name)
                }

                for i in 0..match_indices.len() - 1 {
                    let curr_match = &match_indices[i];
                    let next_match = &match_indices[i + 1];
                    if curr_match.0 + old_sel.len() >= next_match.0 {
                        anyhow::bail!("method `{}` cannot be invoked correctly, please rename this method or modify its signature", fn_name)
                    }
                }

                wasm_content = wasm_content.replace(&old_sel, &new_sel);
            }

            let mut wasm_file = fs::File::create(dest_wasm)?;
            wasm_file.write_all(wasm_content.as_bytes())?;

            let local_abi = abi.get("$local").unwrap();
            let mut abi_file = fs::File::create(dest_abi)?;
            abi_file.write_all(serde_json::to_string(local_abi)?.as_bytes())?;

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

pub(crate) fn execute_build(
    manifest_path: ManifestPath,
    use_gm: bool,
    verbosity_behavior: VerbosityBehavior,
    analysis_behavior: AnalysisBehavior,
    cfg_path: &Option<PathBuf>,
) -> Result<String> {
    let started = Instant::now();

    println!("[1/4] {} Collecting crate metadata", LOOKING_GLASS);
    let crate_metadata = collect_crate_metadata(&manifest_path)?;

    println!("[2/4] {} Building cargo project", TRUCK);
    let build_result = build_cargo_project(
        &crate_metadata,
        use_gm,
        verbosity_behavior,
        analysis_behavior,
        cfg_path,
    )?;

    println!("[3/4] {} Optimizing Wasm bytecode", CLIP);
    optimize_wasm(&crate_metadata)?;

    println!("[4/4] {} Generating ABI file", PAPER);
    generate_abi(&crate_metadata, verbosity_behavior)?;

    if analysis_behavior != AnalysisBehavior::Skip {
        if let Ok(cfa_result) = serde_json::from_str::<'_, Value>(&build_result) {
            let cfa_result = cfa_result.as_object().unwrap();
            let abi_content = fs::read_to_string(&crate_metadata.dest_abi).unwrap();
            let mut origin_abi: Value = serde_json::from_str(&abi_content).unwrap();
            origin_abi
                .as_array_mut()
                .unwrap()
                .iter_mut()
                .for_each(|method| {
                    let method = method.as_object_mut().unwrap();
                    if method.contains_key("name")
                        && method.contains_key("type")
                        && method["type"] == Value::String("function".into())
                    {
                        let method_name = String::from(method["name"].as_str().unwrap());
                        if cfa_result.contains_key(&method_name) {
                            method
                                .insert("conflictFields".into(), cfa_result[&method_name].clone());
                        }
                    }
                });
            let new_abi = serde_json::to_string(&origin_abi).unwrap();
            fs::write(&crate_metadata.dest_abi, new_abi).unwrap();
        } else {
            eprintln!(
                "{}\n{}",
                "unable to parse the result of conflict fields analysis:".yellow(),
                build_result
            );
        }
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
