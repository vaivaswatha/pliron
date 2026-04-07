# LLVM Dialect for [pliron](../README.md)

This crate provides the following functionality:
1. Dialect definitions of LLVM ops, types and attributes.
2. A wrapper around [llvm-sys](https://crates.io/crates/llvm-sys)
  converting to and from our LLVM dialect. This requires
  LLVM to be installed locally.

We currently support LLVM-22 and it needs to be on your computer.
For installing on Debian / Ubuntu, it is recommended to use the
[automatic installation script](https://apt.llvm.org/). If you
prefer to install individual packages, you will need `libllvm22`,
`llvm-22-dev`, `llvm-22-tools`, `clang-22`, `libpolly-22-dev`, etc.

pliron-llvm also provides an [llvm-opt](llvm-opt/README.md) tool.
