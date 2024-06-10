# LLVM Dialect for [pliron](../README.md)

This crate provides the following functionality:
1. Dialect definitions of LLVM ops, types and attributes.
2. A wrapper around [inkwell](https://thedan64.github.io/inkwell/),
  converting b/w our LLVM dialect and `inkwell`'s LLVM representation.

The latter uses [llvm-sys](https://thedan64.github.io/inkwell/),
which requires LLVM to be installed on your system.

We currently support LLVM-17, and hence LLVM-17 needs to be on your computer.
On Ubuntu, this means, you require the `libllvm17` and `libpolly-17-dev`
[packages](https://thedan64.github.io/inkwell/).
