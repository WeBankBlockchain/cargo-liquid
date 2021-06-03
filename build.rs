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

use anyhow::Result;
use std::{
    env,
    ffi::OsStr,
    fs::File,
    io::{Read, Write},
    path::{Path, PathBuf},
};
use walkdir::WalkDir;
use zip::{write::FileOptions, CompressionMethod, ZipWriter};

const DEFAULT_UNIX_PERMISSIONS: u32 = 0o755;

fn main() {
    let manifest_dir: PathBuf = env::var("CARGO_MANIFEST_DIR").unwrap().into();
    let out_dir: PathBuf = env::var("OUT_DIR").unwrap().into();

    let template_dir = manifest_dir.join("template");
    let dst_file = out_dir.join("template.zip");

    println!(
        "Creating template zip: template_dir '{}', destination archive '{}'",
        template_dir.display(),
        dst_file.display(),
    );

    std::process::exit(match zip_dir(&template_dir, &dst_file) {
        Ok(_) => {
            println!(
                "done: {} written to {}",
                template_dir.display(),
                dst_file.display()
            );
            0
        }
        Err(e) => {
            eprintln!("Error: {:?}", e);
            1
        }
    });
}

fn zip_dir(src_dir: &Path, dst_file: &Path) -> Result<()> {
    if !src_dir.exists() {
        anyhow::bail!("src_dir `{}` does not exist", src_dir.display());
    }

    if !src_dir.is_dir() {
        anyhow::bail!("src_dir `{}` is not a directory");
    }

    let file = File::create(dst_file)?;
    let walk_dir = WalkDir::new(src_dir);
    let walk_it = walk_dir.into_iter().filter_map(|e| e.ok());

    let mut zip = ZipWriter::new(file);
    let options = FileOptions::default()
        .compression_method(CompressionMethod::Stored)
        .unix_permissions(DEFAULT_UNIX_PERMISSIONS);

    let mut buffer = Vec::new();
    for entry in walk_it {
        let path = entry.path();
        let mut name = path.strip_prefix(&src_dir)?.to_path_buf();

        // Cargo.toml files cause the folder to excluded from `cargo package` so need to be renamed
        if name.file_name() == Some(OsStr::new("_Cargo.toml")) {
            name.set_file_name("Cargo.toml");
        }

        if let Some(name) = name.to_str() {
            if path.is_file() {
                zip.start_file(name, options)?;
                let mut f = File::open(path)?;
                f.read_to_end(&mut buffer)?;
                zip.write_all(&*buffer)?;
                buffer.clear();
            } else if !name.is_empty() {
                zip.add_directory(name, options)?;
            }
        } else {
            anyhow::bail!("the path contains invalid UTF-8 characters: `{:?}` ", name);
        }
    }
    zip.finish()?;

    Ok(())
}
