#!/bin/bash

# This script runs the CI checks for this workspace.
#
# It differs from .github/workflows/ci.yml as follows
#   - LLVM setup is not performed.
#   - Cargo commands are not passed the additional `--verbose` flag.

set -x
set -e

# Parse command line arguments
WASM_TESTS=false
while [[ $# -gt 0 ]]; do
  case $1 in
  --wasm)
    WASM_TESTS=true
    shift
    ;;
  *)
    echo "Unknown option: $1"
    echo "Usage: $0 [--wasm]"
    exit 1
    ;;
  esac
done

cargo fmt --check
cargo clippy --workspace --all-targets -- -D warnings
RUSTFLAGS="-D warnings" cargo build --workspace
RUSTFLAGS="-D warnings" cargo build -p pliron -p pliron-derive --target wasm32-unknown-unknown
# cargo test --workspace
# cargo test --release --workspace
if [ "$WASM_TESTS" = true ]; then
  cargo test --target wasm32-unknown-unknown
fi
RUSTDOCFLAGS="-D warnings" cargo doc --workspace
