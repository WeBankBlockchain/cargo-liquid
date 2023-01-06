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

use crate::workspace::ManifestPath;
use anyhow::{Context, Result};
use cargo_metadata::{Metadata as CargoMetadata, MetadataCommand, PackageId};
use rustc_version::Channel;

pub fn get_cargo_metadata(manifest_path: &ManifestPath) -> Result<(CargoMetadata, PackageId)> {
    let mut cmd = MetadataCommand::new();
    let metadata = cmd.manifest_path(manifest_path).exec().context(format!(
        "Error invoking `cargo metadata` on {:#?}",
        manifest_path
    ))?;
    let root_packaged_id = metadata
        .resolve
        .as_ref()
        .and_then(|resolve| resolve.root.as_ref())
        .context("Cannot infer the root project id")?
        .clone();

    Ok((metadata, root_packaged_id))
}

pub fn check_channel() -> Result<()> {
    let meta = rustc_version::version_meta()?;
    match meta.channel {
        Channel::Dev | Channel::Nightly => Ok(()),
        _ => {
            anyhow::bail!(
                "cargo-liquid cannot build using the {:?} channel, \
                 switch to nightly.",
                format!("{:?}", meta.channel).to_lowercase(),
            );
        }
    }
}
