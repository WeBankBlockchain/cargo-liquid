# cargo-liquid

## Prerequisite

```bash
rustup toolchain install nightly

git clone https://github.com/vita-dounai/cargo-liquid
cd cargo-liquid
cargo install --path . --force
```

## Usage

```bash
cargo liquid new hello_world
cd hello_world
cargo +nightly liquid build
```
