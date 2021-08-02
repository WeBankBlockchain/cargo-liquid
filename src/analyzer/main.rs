#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(backtrace)]
#![feature(backtrace_frames)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;

mod callbacks;
mod control_flow;
mod ifds;
mod known_names;

use log::*;
use rustc_session::config::ErrorOutputType;
use rustc_session::early_error;
use std::{
    env,
    io::{self, Write},
    process::{self, Command},
};

fn main() {
    let mut args = env::args_os()
        .enumerate()
        .map(|(i, arg)| {
            arg.into_string().unwrap_or_else(|arg| {
                early_error(
                    ErrorOutputType::default(),
                    &format!(
                        "argument {} contains invalid UTF-8 characters: {:?}",
                        i, arg
                    ),
                )
            })
        })
        .collect::<Vec<_>>();
    assert!(!args.is_empty());
    args.remove(0);

    let project_name = env::var("LIQUID_ANALYSIS_PROJECT");
    if let Ok(project_name) = project_name {
        if args
            .iter()
            .enumerate()
            .any(|(i, arg)| arg == &"--crate-name" && args.get(i + 1) == Some(&project_name))
        {
            if env::var("RUST_LOG").is_ok() {
                let mut builder = env_logger::Builder::from_default_env();
                builder.target(env_logger::Target::Stderr);
                builder.init();
                rustc_driver::init_rustc_env_logger();
            }
            rustc_driver::install_ice_hook();

            let result = rustc_driver::catch_fatal_errors(|| {
                info!("analysis process started");
                debug!("command provided for analysis: {:?}", args.join(" "));

                let always_encode_mir = String::from("always-encode-mir");
                if !args.iter().any(|arg| arg.ends_with(&always_encode_mir)) {
                    args.push("-Z".into());
                    args.push(always_encode_mir);
                }

                let cfg_path = std::env::var("LIQUID_ANALYSIS_CFG_PATH")
                    .ok()
                    .map(|path| path.into());
                let mut callbacks = callbacks::AnalysisCallbacks { cfg_path };

                // In practice, when starting compiling process, the rustc_driver
                // will remove the first command line argument automatically. This
                // behavior may be changed in future, be careful.
                let compiler = rustc_driver::RunCompiler::new(&args, &mut callbacks);
                compiler.run()
            });

            let exit_code = if matches!(result, Ok(_)) {
                info!("analysis process executed successfully");
                rustc_driver::EXIT_SUCCESS
            } else {
                warn!("analysis process executed unsuccessfully");
                rustc_driver::EXIT_FAILURE
            };
            process::exit(exit_code);
        }
    }

    let output = Command::new(&args[0])
        .args(&args[1..])
        .output()
        .expect(&format!("fail to execute command `{}`", args.join(" ")));
    io::stdout().write(&output.stdout).unwrap();
    io::stderr().write(&output.stderr).unwrap();
    process::exit(output.status.code().unwrap());
}
