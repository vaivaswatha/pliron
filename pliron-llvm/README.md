# LLVM Dialect for [pliron](../README.md)

This crate provides the following functionality:
1. Dialect definitions of LLVM ops, types and attributes.
2. A wrapper around [llvm-sys](https://crates.io/crates/llvm-sys)
  converting to and from our LLVM dialect. This necessitates
  that LLVM be installed locally.

We currently support LLVM-20, and hence LLVM-20 needs to be on your computer.
On Ubuntu, this means, you require the `libllvm20` and `libpolly-20-dev`
[packages](https://apt.llvm.org/).

pliron-llvm also provides an [llvm-opt](llvm-opt/README.md) tool.

**Note**: Implementation of the LLVM dialect is in-progress, not yet complete.