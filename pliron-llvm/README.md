# LLVM Dialect for [pliron](../README.md)

This crate provides the following functionality:
1. Dialect definitions of LLVM ops, types and attributes.
2. A wrapper around [llvm-sys](https://crates.io/crates/llvm-sys)
  converting to and from our LLVM dialect. This necessitates
  that LLVM be installed locally.

We currently support LLVM-21 and it needs to be on your computer.
For installing on Debian / Ubuntu, it is recommended to use the
[automatic installation script](https://apt.llvm.org/). If you
prefer to install individual packages, you will need `libllvm21`,
`llvm-21-dev`, `llvm-21-tools`, `clang-21`, `libpolly-21-dev`, etc.

pliron-llvm also provides an [llvm-opt](llvm-opt/README.md) tool.

**Note**: Implementation of the LLVM dialect is in-progress, not yet complete.