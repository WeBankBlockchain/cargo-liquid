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

mod cmd;
mod utils;
mod workspace;

use anyhow::{Error, Result};
use colored::Colorize;
use std::{
    convert::{TryFrom, TryInto},
    path::PathBuf,
};
use structopt::{clap, StructOpt};
use workspace::ManifestPath;

#[derive(StructOpt)]
#[structopt(bin_name = "cargo")]
pub(crate) enum Opts {
    /// Utilities to develop liquid project.
    #[structopt(name = "liquid")]
    #[structopt(setting = clap::AppSettings::UnifiedHelpMessage)]
    #[structopt(setting = clap::AppSettings::DeriveDisplayOrder)]
    #[structopt(setting = clap::AppSettings::DontCollapseArgsInUsage)]
    Args(Args),
}

#[derive(StructOpt)]
pub(crate) struct Args {
    #[structopt(subcommand)]
    cmd: Command,
}

#[derive(StructOpt)]
struct VerbosityFlags {
    /// No output printed to stdout.
    #[structopt(short, long)]
    quiet: bool,
    /// Uses verbose output.
    #[structopt(long)]
    verbose: bool,
}

#[derive(Copy, Clone)]
enum VerbosityBehavior {
    Quiet,
    Verbose,
}

#[derive(StructOpt)]
struct AnalysisFlags {
    /// If this flag is set, the analysis process will be skipped unconditionally.
    #[structopt(long)]
    skip_analysis: bool,
}

#[derive(PartialEq, Eq, Copy, Clone)]
enum AnalysisBehavior {
    Enforce,
    Skip,
}

impl From<VerbosityBehavior> for xargo_lib::Verbosity {
    fn from(behavior: VerbosityBehavior) -> Self {
        match behavior {
            VerbosityBehavior::Verbose => Self::Verbose,
            VerbosityBehavior::Quiet => Self::Quiet,
        }
    }
}

impl TryFrom<&VerbosityFlags> for VerbosityBehavior {
    type Error = Error;

    fn try_from(value: &VerbosityFlags) -> Result<Self, Self::Error> {
        match (value.quiet, value.verbose) {
            (true, false) => Ok(VerbosityBehavior::Quiet),
            (false, false) => Ok(VerbosityBehavior::Quiet),
            (false, true) => Ok(VerbosityBehavior::Verbose),
            (true, true) => anyhow::bail!("Cannot pass both --quiet and --verbose flags"),
        }
    }
}

impl TryFrom<&AnalysisFlags> for AnalysisBehavior {
    type Error = Error;

    fn try_from(value: &AnalysisFlags) -> Result<Self, Self::Error> {
        if value.skip_analysis {
            Ok(AnalysisBehavior::Skip)
        } else {
            Ok(AnalysisBehavior::Enforce)
        }
    }
}

// Since 1.40, cargo had stabilized a new feature named as `cache-messages`,
// which caching all compiler's output into a local file mandatorily. When
// cargo detects that there is no changing in dependents or source code, it
// will simply redisplay the cached message to accelerate the building
// process.
//
// This feature works fine in most of situation. But unfortunately, cargo will
// cache the log produced by liquid-analy as well (because liquid-analy works
// by inserting analysis callbacks into the compiler). This causes cargo
// unconditionally displaying stale messages from the analyzer even the analyzer
// never be started, which is sometimes misleading.
//
// By default, we will force cargo to start a new compiling session. If you don't want
// to compile again, you can turn`enforce_analysis` flag on.
#[derive(StructOpt)]
enum Command {
    /// Sets up and creates a new liquid project.
    #[structopt(name = "new")]
    New {
        /// The type of the project, must be `contract` or `collaboration`.
        ty: String,
        /// The name of the newly created project.
        name: String,
        /// The optional target directory for the newly created project.
        #[structopt(short, long, parse(from_os_str))]
        target_dir: Option<PathBuf>,
    },
    /// Builds the project.
    #[structopt(name = "build")]
    Build {
        #[structopt(flatten)]
        verbosity_flags: VerbosityFlags,
        /// Indicates using GM mode or not.
        #[structopt(short, long)]
        gm: bool,
        /// Indicates the manifest to use, must be a Cargo.toml file.
        #[structopt(short, long)]
        manifest_path: Option<PathBuf>,
        #[structopt(flatten)]
        analysis_flags: AnalysisFlags,
        /// If this flag is set, the analysis process will produce the whole call graph in dot format.
        #[structopt(short, long)]
        dump_cfg: Option<PathBuf>,
    },

    ///Rename the project , you need to update name in the cargo-liquid dir and promise the project exits in that.
    #[structopt(name = "rename")]
    Rename {
        //The project old name
        old_name: String,
        //The project new name
        new_name: String,
    },
}

fn main() {
    let Opts::Args(args) = Opts::from_args();
    match exec(args.cmd) {
        Ok(msg) => println!("{}", msg.bold()),
        Err(err) => eprintln!("{} {}", "ERROR:".bright_red().bold(), format!("{:?}", err)),
    }
}

fn exec(cmd: Command) -> Result<String> {
    match &cmd {
        Command::New {
            ty,
            name,
            target_dir,
        } => cmd::execute_new(ty, name, target_dir.as_ref()),
        Command::Build {
            verbosity_flags,
            gm,
            manifest_path,
            dump_cfg,
            analysis_flags,
        } => cmd::execute_build(
            manifest_path
                .as_ref()
                .map_or(Default::default(), |manifest_path| {
                    ManifestPath::new(manifest_path).expect("invalid manifest path")
                }),
            *gm,
            verbosity_flags.try_into()?,
            analysis_flags.try_into()?,
            dump_cfg,
        ),
        Command::Rename { old_name, new_name } => cmd::execute_rename(old_name, new_name),
    }
}
