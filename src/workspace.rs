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

use anyhow::{Context, Result};
use cargo_metadata::{Metadata as CargoMetadata, Package, PackageId};
use std::{
    collections::{HashMap, HashSet},
    convert::{TryFrom, TryInto},
    fs,
    path::{Path, PathBuf, MAIN_SEPARATOR},
};
use toml::value;

const MANIFEST_FILE: &str = "Cargo.toml";

#[derive(Clone, Debug)]
pub struct ManifestPath {
    path: PathBuf,
}

impl ManifestPath {
    /// Create a new ManifestPath, errors if not path to `Cargo.toml`
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self> {
        let manifest = path.as_ref();
        if let Some(file_name) = manifest.file_name() {
            if file_name != MANIFEST_FILE {
                anyhow::bail!("Manifest file must be a Cargo.toml")
            }
        }
        Ok(ManifestPath {
            path: manifest.into(),
        })
    }
}

impl TryFrom<&PathBuf> for ManifestPath {
    type Error = anyhow::Error;

    fn try_from(value: &PathBuf) -> Result<Self, Self::Error> {
        ManifestPath::new(value)
    }
}

impl Default for ManifestPath {
    fn default() -> ManifestPath {
        ManifestPath::new(MANIFEST_FILE).unwrap()
    }
}

impl From<&ManifestPath> for PathBuf {
    fn from(manifest_path: &ManifestPath) -> Self {
        manifest_path.path.clone()
    }
}

impl AsRef<Path> for ManifestPath {
    fn as_ref(&self) -> &Path {
        self.path.as_ref()
    }
}

/// Create, amend and save a copy of the specified `Cargo.toml`.
pub struct Manifest {
    path: ManifestPath,
    toml: value::Table,
}

impl Manifest {
    /// Create new CargoToml for the given manifest path.
    ///
    /// The path *must* be to a `Cargo.toml`.
    pub fn new<P>(path: P) -> Result<Manifest>
    where
        P: TryInto<ManifestPath, Error = anyhow::Error>,
    {
        let manifest_path = path.try_into()?;
        let toml = fs::read_to_string(&manifest_path).context("Loading Cargo.toml")?;
        let toml: value::Table = toml::from_str(&toml)?;

        Ok(Manifest {
            path: manifest_path,
            toml,
        })
    }

    /// Remove a value from the `[lib] crate-types = []` section
    ///
    /// If the value does not exist, does nothing.
    pub fn with_removed_crate_type(&mut self, crate_type: &str) -> Result<&mut Self> {
        let crate_types = self.get_crate_types_mut()?;
        if crate_type_exists(crate_type, crate_types) {
            crate_types.retain(|v| v.as_str().map_or(true, |s| s != crate_type));
        }
        Ok(self)
    }

    /// Add a value to the `[lib] crate-types = []` section.
    ///
    /// If the value already exists, does nothing.
    pub fn with_added_crate_type(&mut self, crate_type: &str) -> Result<&mut Self> {
        let crate_types = self.get_crate_types_mut()?;
        if !crate_type_exists(crate_type, crate_types) {
            crate_types.push(crate_type.into());
        }
        Ok(self)
    }

    /// Set `[profile.release]` lto flag
    pub fn with_profile_release_lto(&mut self, enabled: bool) -> Result<&mut Self> {
        let profile = self
            .toml
            .entry("profile")
            .or_insert(value::Value::Table(Default::default()));
        let release = profile
            .as_table_mut()
            .ok_or_else(|| anyhow::anyhow!("profile should be a table"))?
            .entry("release")
            .or_insert(value::Value::Table(Default::default()));
        let lto = release
            .as_table_mut()
            .ok_or_else(|| anyhow::anyhow!("release should be a table"))?
            .entry("lto")
            .or_insert(enabled.into());
        *lto = enabled.into();
        Ok(self)
    }

    /// Get mutable reference to `[lib] crate-types = []` section
    fn get_crate_types_mut(&mut self) -> Result<&mut value::Array> {
        let lib = self
            .toml
            .get_mut("lib")
            .ok_or_else(|| anyhow::anyhow!("lib section not found"))?;
        let crate_types = lib
            .get_mut("crate-type")
            .ok_or_else(|| anyhow::anyhow!("crate-type section not found"))?;

        crate_types
            .as_array_mut()
            .ok_or_else(|| anyhow::anyhow!("crate-types should be an Array"))
    }

    /// Writes the amended manifest to the given path.
    pub fn write(&self, path: &ManifestPath) -> Result<()> {
        let manifest_path = path.as_ref();

        if let Some(dir) = manifest_path.parent() {
            fs::create_dir_all(&dir).context(format!("Creating directory '{}'", dir.display()))?;
        }

        let updated_toml = toml::to_string(&self.toml)?;
        fs::write(&manifest_path, updated_toml)?;
        Ok(())
    }

    /// Replace relative paths with absolute paths with the working directory.
    ///
    /// Enables the use of a temporary amended copy of the manifest.
    ///
    /// # Rewrites
    ///
    /// - `[lib]/path`
    /// - `[dependencies]`
    ///
    /// Dependencies with package names specified in `exclude_deps` will not be rewritten.
    fn rewrite_relative_paths<I, S>(&mut self, exclude_deps: I) -> Result<&mut Self>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let abs_path = self.path.as_ref().canonicalize()?;
        let abs_dir = abs_path
            .parent()
            .expect("The manifest path is a file path so has a parent");

        let to_absolute = |value_id: String, existing_path: &mut value::Value| -> Result<()> {
            let path_str = existing_path
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("{} should be a string", value_id))?;
            let path = PathBuf::from(path_str);
            if path.is_relative() {
                let lib_abs = abs_dir.join(path);
                *existing_path = value::Value::String(lib_abs.to_string_lossy().into())
            }
            Ok(())
        };

        let rewrite_path = |table_value: &mut value::Value, table_section: &str, default: &str| {
            let table = table_value.as_table_mut().ok_or_else(|| {
                anyhow::anyhow!("'[{}]' section should be a table", table_section)
            })?;

            match table.get_mut("path") {
                Some(existing_path) => {
                    to_absolute(format!("[{}]/path", table_section), existing_path)
                }
                None => {
                    let default_path = PathBuf::from(default);
                    if !default_path.exists() {
                        anyhow::bail!(
                            "No path specified, and the default `{}` was not found",
                            default
                        )
                    }
                    let path = abs_dir.join(default_path);
                    table.insert(
                        "path".into(),
                        value::Value::String(path.to_string_lossy().into()),
                    );
                    Ok(())
                }
            }
        };

        // Rewrite `[lib] path = /path/to/lib.rs`
        if let Some(lib) = self.toml.get_mut("lib") {
            rewrite_path(
                lib,
                "lib",
                &["src", "lib.rs"].join(&MAIN_SEPARATOR.to_string()),
            )?;
        }

        // Rewrite `[[bin]] path = /path/to/main.rs`
        if let Some(bin) = self.toml.get_mut("bin") {
            let bins = bin
                .as_array_mut()
                .ok_or_else(|| anyhow::anyhow!("'[[bin]]' section should be a table array"))?;

            // Rewrite `[[bin]] path =` value to an absolute path.
            for bin in bins {
                rewrite_path(
                    bin,
                    "[bin]",
                    &["src", "main.rs"].join(&MAIN_SEPARATOR.to_string()),
                )?;
            }
        }

        // Rewrite any dependency relative paths
        if let Some(dependencies) = self.toml.get_mut("dependencies") {
            let exclude = exclude_deps
                .into_iter()
                .map(|s| s.as_ref().to_string())
                .collect::<HashSet<_>>();
            let table = dependencies
                .as_table_mut()
                .ok_or_else(|| anyhow::anyhow!("dependencies should be a table"))?;
            for (name, value) in table {
                let package_name = {
                    let package = value.get("package");
                    let package_name = package.and_then(|p| p.as_str()).unwrap_or(name);
                    package_name.to_string()
                };

                if !exclude.contains(&package_name) {
                    if let Some(dependency) = value.as_table_mut() {
                        if let Some(dep_path) = dependency.get_mut("path") {
                            to_absolute(format!("dependency {}", package_name), dep_path)?;
                        }
                    }
                }
            }
        }

        Ok(self)
    }
}

#[allow(clippy::ptr_arg)]
fn crate_type_exists(crate_type: &str, crate_types: &value::Array) -> bool {
    crate_types
        .iter()
        .any(|v| v.as_str().map_or(false, |s| s == crate_type))
}

/// Make a copy of a cargo workspace, maintaining only the directory structure and manifest
/// files. Relative paths to source files and non-workspace dependencies are rewritten to absolute
/// paths to the original locations.
///
/// This allows custom amendments to be made to the manifest files without editing the originals
/// directly.
pub struct Workspace {
    workspace_root: PathBuf,
    root_package: PackageId,
    members: HashMap<PackageId, (Package, Manifest)>,
}

impl Workspace {
    /// Create a new Workspace from the supplied cargo metadata.
    pub fn new(metadata: &CargoMetadata, root_package: &PackageId) -> Result<Self> {
        let member_manifest = |package_id: &PackageId| -> Result<(PackageId, (Package, Manifest))> {
            let package = metadata
                .packages
                .iter()
                .find(|p| p.id == *package_id)
                .unwrap_or_else(|| {
                    panic!(
                        "Package '{}' is a member and should be in the packages list",
                        package_id
                    )
                });
            let manifest = Manifest::new(&package.manifest_path)?;
            Ok((package_id.clone(), (package.clone(), manifest)))
        };

        let members = metadata
            .workspace_members
            .iter()
            .map(member_manifest)
            .collect::<Result<HashMap<_, _>>>()?;

        if !members.contains_key(root_package) {
            anyhow::bail!("The root package should be a workspace member")
        }

        Ok(Workspace {
            workspace_root: metadata.workspace_root.clone(),
            root_package: root_package.clone(),
            members,
        })
    }

    /// Amend the root package manifest using the supplied function.
    ///
    /// # Note
    ///
    /// The root package is the current workspace package being built, not to be confused with
    /// the workspace root (where the top level workspace Cargo.toml is defined).
    pub fn with_root_package_manifest<F>(&mut self, f: F) -> Result<&mut Self>
    where
        F: FnOnce(&mut Manifest) -> Result<()>,
    {
        let root_package_manifest = self
            .members
            .get_mut(&self.root_package)
            .map(|(_, m)| m)
            .expect("The root package should be a workspace member");
        f(root_package_manifest)?;
        Ok(self)
    }

    /// Copy the workspace with amended manifest files to a temporary directory, executing the
    /// supplied function with the root manifest path before the directory is cleaned up.
    pub fn using_temp<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(&ManifestPath) -> Result<()>,
    {
        let tmp_dir = tempfile::Builder::new()
            .prefix(".cargo-contract_")
            .tempdir()?;
        let new_paths = self.write(&tmp_dir)?;
        let root_manifest_path = new_paths
            .iter()
            .find_map(|(pid, path)| {
                if *pid == self.root_package {
                    Some(path)
                } else {
                    None
                }
            })
            .expect("root package should be a member of the temp workspace");
        f(root_manifest_path)
    }

    /// Writes the amended manifests to the `target` directory, retaining the workspace directory
    /// structure, but only with the `Cargo.toml` files.
    ///
    /// Relative paths will be rewritten to absolute paths from the original workspace root, except
    /// intra-workspace relative dependency paths which will be preserved.
    ///
    /// Returns the paths of the new manifests.
    pub fn write<P: AsRef<Path>>(&mut self, target: P) -> Result<Vec<(PackageId, ManifestPath)>> {
        let exclude_member_package_names = self
            .members
            .iter()
            .map(|(_, (p, _))| p.name.clone())
            .collect::<Vec<_>>();
        let mut new_manifest_paths = Vec::new();
        for (package_id, (package, manifest)) in self.members.iter_mut() {
            // replace the original workspace root with the temporary directory
            let mut new_path: PathBuf = target.as_ref().into();
            new_path.push(package.manifest_path.strip_prefix(&self.workspace_root)?);
            let new_manifest = ManifestPath::new(new_path)?;

            manifest.rewrite_relative_paths(&exclude_member_package_names)?;
            manifest.write(&new_manifest)?;

            new_manifest_paths.push((package_id.clone(), new_manifest));
        }
        Ok(new_manifest_paths)
    }
}
