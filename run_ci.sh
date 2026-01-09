#!/bin/bash

# This script runs the CI checks for this workspace.
#
# It differs from .github/workflows/ci.yml as follows
#   - LLVM setup is not performed.
#   - Cargo commands are not passed the additional `--verbose` flag.

set -x
set -e

cargo fmt --check
cargo clippy --workspace --all-targets -- -D warnings
RUSTFLAGS="-D warnings" cargo build --workspace
RUSTFLAGS="-D warnings" cargo build -p pliron -p pliron-derive --target wasm32-unknown-unknown
cargo test --workspace
cargo test --release --workspace
RUSTDOCFLAGS="-D warnings" cargo doc --workspace
