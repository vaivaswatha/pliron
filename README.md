# Programming Languages Intermediate RepresentatiON

[![Status](https://github.com/vaivaswatha/pliron/actions/workflows/ci.yml/badge.svg)](https://github.com/vaivaswatha/pliron/actions/workflows/ci.yml)

`pliron` is an extensible compiler IR framework, inspired by [MLIR](https://mlir.llvm.org/docs/LangRef/)
and written in safe Rust.

## Build and Test
* Install the [rust toolchain](https://www.rust-lang.org/tools/install).
* `cargo build` and `cargo test` should build the compiler and run the testsuite.
* To see a simple IR constructed (by the [print_simple](tests/ir_construct.rs) test),
  use the following command:

      cargo test print_simple -- --show-output

  It should print something like:
  ```mlir
  builtin.module @bar {
    block_0_0():
      builtin.func @foo: builtin.function <() -> (builtin.integer <si64>)> {
        entry():
          c0 = builtin.constant 0x0: builtin.integer <si64>
          llvm.return c0
      }
  }
  ```

## Using the Library
`pliron` is currently in a nascent stage and not yet useful for
real-world use. In the future it can be used by just adding
a dependence to the [crate](https://crates.io/crates/pliron)
in your Rust project.

## Documentation
* Some key design decisions are explained in the
  [introductory blog article](https://github.com/vaivaswatha/pliron/wiki/Introducing-pliron).
* Code documentation can be found on
  [docs.rs](https://docs.rs/pliron/latest/pliron/).
