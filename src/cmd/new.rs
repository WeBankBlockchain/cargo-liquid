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
use heck::CamelCase;
use std::{
    env, fs,
    io::{Cursor, Read, Seek, SeekFrom, Write},
    path::PathBuf,
};

pub(crate) fn execute_new(name: &str, dir: Option<&PathBuf>) -> Result<String> {
    if name.contains('-') {
        anyhow::bail!("Contract names cannot contain hyphens");
    }

    let out_dir = dir.unwrap_or(&env::current_dir()?).join(name);
    if out_dir.join("Cargo.toml").exists() {
        anyhow::bail!("A Cargo package already exists in {}", name);
    }

    if !out_dir.exists() {
        fs::create_dir(&out_dir)?;
    }

    let template = include_bytes!(concat!(env!("OUT_DIR"), "/template.zip"));
    let mut cursor = Cursor::new(Vec::new());
    cursor.write_all(template)?;
    cursor.seek(SeekFrom::Start(0))?;

    let mut archive = zip::ZipArchive::new(cursor)?;
    for i in 0..archive.len() {
        let mut file = archive.by_index(i)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;

        let contents = contents
            .replace("{{name}}", name)
            .replace("{{camel_name}}", &name.to_camel_case());
        #[allow(deprecated)]
        let out_path = out_dir.join(file.sanitized_name());

        if (&*file.name()).ends_with('/') {
            fs::create_dir_all(&out_path)?;
        } else {
            if let Some(p) = out_path.parent() {
                if !p.exists() {
                    fs::create_dir_all(&p)?;
                }
            }

            let mut out_file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(out_path.clone())
                .map_err(|e| {
                    #[allow(deprecated)]
                    let sanitized_name = file.sanitized_name();
                    if e.kind() == std::io::ErrorKind::AlreadyExists {
                        anyhow::anyhow!(
                            "New contract file {} already exists",
                            sanitized_name.display()
                        )
                    } else {
                        anyhow::anyhow!(e)
                    }
                })?;

            out_file.write_all(contents.as_bytes())?;
        }

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;

            if let Some(mode) = file.unix_mode() {
                fs::set_permissions(&out_path, fs::Permissions::from_mode(mode))?
            }
        }
    }

    Ok(format!("Contract {} created", name))
}
