#!/bin/bash

# This script runs the CI checks for this workspace.
#
# It differs from .github/workflows/ci.yml as follows
#   - LLVM setup is not performed.
#   - Cargo commands are not passed the additional `--verbose` flag.

set -x
set -e

RUSTFLAGS="-D warnings" cargo build --workspace
cargo test --workspace
cargo test --release --workspace
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --check
RUSTDOCFLAGS="-D warnings" cargo doc --workspace
