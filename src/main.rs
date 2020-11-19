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

#[derive(StructOpt)]
#[structopt(bin_name = "cargo")]
pub(crate) enum Opts {
    /// Utilities to develop Liquid smart contracts
    #[structopt(name = "liquid")]
    #[structopt(setting = clap::AppSettings::UnifiedHelpMessage)]
    #[structopt(setting = clap::AppSettings::DeriveDisplayOrder)]
    #[structopt(setting = clap::AppSettings::DontCollapseArgsInUsage)]
    Contract(ContractArgs),
}

#[derive(StructOpt)]
pub(crate) struct ContractArgs {
    #[structopt(subcommand)]
    cmd: Command,
}

#[derive(StructOpt)]
struct VerbosityFlags {
    #[structopt(long)]
    quiet: bool,
    #[structopt(long)]
    verbose: bool,
}

enum Verbosity {
    Quiet,
    Verbose,
}

impl TryFrom<&VerbosityFlags> for Option<Verbosity> {
    type Error = Error;

    fn try_from(value: &VerbosityFlags) -> Result<Self, Self::Error> {
        match (value.quiet, value.verbose) {
            (true, false) => Ok(Some(Verbosity::Quiet)),
            (false, false) => Ok(Some(Verbosity::Quiet)),
            (false, true) => Ok(Some(Verbosity::Verbose)),
            (true, true) => anyhow::bail!("Cannot pass both --quiet and --verbose flags"),
        }
    }
}

#[derive(StructOpt)]
enum Command {
    /// Setup and create a new smart contract project
    #[structopt(name = "new")]
    New {
        /// The name of the newly created smart contract
        name: String,
        /// The optional target directory for the contract project
        #[structopt(short, long, parse(from_os_str))]
        target_dir: Option<PathBuf>,
    },
    /// Compiles the smart contract
    #[structopt(name = "build")]
    Build {
        #[structopt(flatten)]
        verbosity: VerbosityFlags,
        #[structopt(short, long, help = "Indicates using GM mode or not")]
        gm: bool,
    },
}

fn main() {
    let Opts::Contract(args) = Opts::from_args();
    match exec(args.cmd) {
        Ok(msg) => println!("{}", msg.bold()),
        Err(err) => eprintln!("{} {}", "ERROR:".bright_red().bold(), format!("{:?}", err)),
    }
}

fn exec(cmd: Command) -> Result<String> {
    match &cmd {
        Command::New { name, target_dir } => cmd::execute_new(name, target_dir.as_ref()),
        Command::Build { verbosity, gm } => {
            cmd::execute_build(Default::default(), *gm, verbosity.try_into()?)
        }
    }
}
