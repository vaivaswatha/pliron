# Programming Languages Intermediate RepresentatiON

[![Status](https://github.com/vaivaswatha/pliron/actions/workflows/ci.yml/badge.svg)](https://github.com/vaivaswatha/pliron/actions/workflows/ci.yml)

`pliron` is an extensible intermediate representation framework for programming languages,
inspired by [MLIR](https://mlir.llvm.org/docs/LangRef/) and written in safe Rust.

## Build and Test
* Install the [rust toolchain](https://www.rust-lang.org/tools/install).
* `cargo build` and `cargo test` should build the compiler and run the testsuite.
* To see a simple IR constructed (from the [const_ret_in_mod](tests/ir_construct.rs) test),
  use the following command:

      cargo test const_ret_in_mod -- --show-output

  It should print something like:
  ```mlir
  builtin.module @bar {
  block_0_0():
    builtin.func @foo() -> () {
      entry():
        c0 = builtin.constant 0x0: si64
        llvm.return c0
    }
  }
  ```

## Using the Library
`pliron` is currently in a nascent stage and not yet useful for
real-world use. In the future it can be used by just adding
a dependence to the [crate](https://crates.io/crates/pliron)
in your Rust project.
