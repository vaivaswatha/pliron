# LLVM Dialect for [pliron](../README.md)

This crate provides the following functionality:
1. Dialect definitions of LLVM ops, types and attributes.
2. A wrapper around [llvm-sys](https://crates.io/crates/llvm-sys)
  converting to and from our LLVM dialect. This necessitates
  that LLVM be installed locally.

We currently support LLVM-18, and hence LLVM-18 needs to be on your computer.
On Ubuntu, this means, you require the `libllvm18` and `libpolly-18-dev`
[packages](https://apt.llvm.org/).

## llvm-opt tool
The `llvm-opt` binary is provided to enable parsing LLVM bitcode binaries
into `pliron`'s LLVM dialect and to emit LLVM bitcode back from the dialect.

Example usage:
1. Compile [fib.c](tests/resources/fib.c) into LLVM-IR:
  
    `$clang-18 -c -emit-llvm -o /tmp/fib.bc tests/resources/fib.c `

2. Convert the LLVM bitcode to LLVM dialect in `pliron` and back to
LLVM bitcode (the binary `llvm-opt`, produced in your cargo's target
directory must be in $PATH):

    `$llvm-opt -S -i /tmp/fib.bc -o /tmp/fib.opt.ll`

3. Compile the output fibonacci LLVM-IR, along with a
[main function](tests/resources/fib-main.c) into a binary:

    `$clang-18 -o /tmp/fib /tmp/fib.out.ll tests/resources/fib-main.c`

4. Run the fibonacci binary to see the first few fibonacci numbers
printed.

    `$/tmp/fib`

    ```
        fib(0): 0
        fib(1): 0
        fib(2): 1
        fib(3): 1
        fib(4): 2
    ```

**Note**: Implementation of the LLVM dialect is not complete, and the above is just a proof-of-concept.