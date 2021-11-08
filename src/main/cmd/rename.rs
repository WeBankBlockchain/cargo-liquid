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
use std::{env, fs};

pub(crate) fn update_file(old_str: &str, new_str: &str, file_path: &str) {
    let mut contents = fs::read_to_string(file_path).expect(&format!(
        "Something went wrong reading the file {}",
        file_path
    ));
    contents = contents.replace(old_str, new_str);
    fs::write(file_path, contents).expect(&format!(
        "Something went wrong write the file {}",
        file_path
    ));
}

pub(crate) fn execute_rename(old_name: &str, new_name: &str) -> Result<String> {
    if new_name.contains('-') {
        anyhow::bail!("Project new_names cannot contain hyphens");
    }
    if old_name.contains('-') {
        anyhow::bail!("Project names cannot contain hyphens");
    }
    let out_dir = env::current_dir().unwrap().join(old_name);

    if !out_dir.join("Cargo.toml").exists() {
        anyhow::bail!(
            "A Cargo package not exists in {} {}",
            old_name,
            out_dir.join("Cargo.toml").display()
        );
    }
    if !out_dir.join(".liquid/abi_gen/Cargo.toml").exists() {
        anyhow::bail!("A .liquid/abi_gen/Cargo package not exists in {}", old_name);
    }
    if !out_dir.join(".liquid/abi_gen/main.rs").exists() {
        anyhow::bail!(
            "A .liquid/abi_gen/main.rs package not exists in {}",
            old_name
        );
    }

    let cargo_file_path = &out_dir
        .join("Cargo.toml")
        .to_path_buf()
        .into_os_string()
        .into_string()
        .unwrap();
    let mut old_str = "name = \"".to_string();
    let mut new_str = "name = \"".to_string();
    old_str += old_name;
    new_str += new_name;
    update_file(&old_str, &new_str, cargo_file_path);

    let abi_cargo_file_path = &out_dir
        .join(".liquid/abi_gen/Cargo.toml")
        .to_path_buf()
        .into_os_string()
        .into_string()
        .unwrap();
    let mut old_str = "package = \"".to_string();
    let mut new_str = "package = \"".to_string();
    old_str += old_name;
    new_str += new_name;
    update_file(&old_str, &new_str, abi_cargo_file_path);

    let abi_main_file_path = &out_dir
        .join(".liquid/abi_gen/main.rs")
        .to_path_buf()
        .into_os_string()
        .into_string()
        .unwrap();

    let mut old_str = "std::fs::write(\"".to_string();
    let mut new_str = "std::fs::write(\"".to_string();
    old_str += old_name;
    new_str += new_name;
    update_file(&old_str, &new_str, abi_main_file_path);

    fs::rename(
        env::current_dir().unwrap().join(old_name),
        env::current_dir().unwrap().join(new_name),
    )
    .expect(&format!(
        "rename dir {} to dir {} error",
        old_name, new_name
    ));

    Ok(format!("Project  rename"))
}
