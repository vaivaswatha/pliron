use std::{env, path::PathBuf, process::Output, sync::LazyLock};

use assert_cmd::{Command, cargo::cargo_bin_cmd};
use cargo_manifest::Manifest;
use expect_test::expect;
use tempfile::tempdir;

const CLANG_BINARY: LazyLock<PathBuf> = LazyLock::new(|| {
    // Read Cargo.toml from pliron-llvm to get the llvm-sys version.
    let manifest = Manifest::from_path(env!("CARGO_MANIFEST_DIR").to_string() + "/../Cargo.toml")
        .expect("Could not read pliron-llvm Cargo.toml");
    let lli_version = manifest.dependencies.expect("Expected llvm-sys dependency")["llvm-sys"]
        .req()
        .to_string();
    assert!(
        lli_version.len() == 3,
        "Unexpected llvm-sys version format: Expected two-digit major version and one digit minor version, got {}",
        lli_version
    );
    format!("clang-{}", &lli_version[..2]).into()
});

static RESOURCES_DIR: LazyLock<PathBuf> = LazyLock::new(|| {
    [env!("CARGO_MANIFEST_DIR"), "tests", "resources"]
        .iter()
        .collect()
});

/// Utility to compile and run a C file through Pliron-IR.
/// 1. C file to LLVM-IR
/// 2. LLVM-IR -> Pliron's LLVM dialect -> LLVM-IR
/// 3. Compile the result LLVM-IR to an executable
/// 4. Run the executable and return the Output
fn c_clang_ir_pliron_ir_exe(input_c_file: &str) -> Output {
    // Create a tempdir() to place the temporary compiled files.
    let tmp_dir = tempdir().unwrap();

    // clang -S -emit-llvm -o $tmp/input.ll $input_c_file
    let mut cmd = Command::new(CLANG_BINARY.clone());
    let compile_c = cmd
        .current_dir(&*RESOURCES_DIR)
        .args([
            "-S",
            "-emit-llvm",
            "-o",
            tmp_dir.path().join("input.ll").to_str().unwrap(),
            input_c_file,
        ])
        .output()
        .expect("failed to execute clang to compile C to LLVM-IR");
    assert!(
        compile_c.status.success(),
        "{}",
        String::from_utf8(compile_c.stderr).unwrap()
    );

    // llvm-opt -o $tmp/input.pliron.ll -S $tmp/input.ll
    let mut cmd = cargo_bin_cmd!("llvm-opt");
    let compile_pliron = cmd
        .current_dir(&*RESOURCES_DIR)
        .args([
            "-o",
            tmp_dir.path().join("input.pliron.ll").to_str().unwrap(),
            "-S",
            "-i",
            tmp_dir.path().join("input.ll").to_str().unwrap(),
        ])
        .output()
        .expect("failed to execute llvm-opt to compile LLVM-IR via pliron");
    assert!(
        compile_pliron.status.success(),
        "{}",
        String::from_utf8(compile_pliron.stderr).unwrap()
    );

    // clang -o $tmp/input.exe $tmp/input.pliron.ll
    let mut cmd = Command::new(CLANG_BINARY.clone());
    let compile_exe = cmd
        .current_dir(&*RESOURCES_DIR)
        .args([
            "-o",
            tmp_dir.path().join("input.exe").to_str().unwrap(),
            tmp_dir.path().join("input.pliron.ll").to_str().unwrap(),
        ])
        .output()
        .expect("failed to execute clang to final LLVM-IR to executable");
    assert!(
        compile_exe.status.success(),
        "{}",
        String::from_utf8(compile_exe.stderr).unwrap()
    );

    // $tmp/input.exe
    let mut cmd = Command::new(tmp_dir.path().join("input.exe"));
    cmd.output().expect("Error executing compiled program")
}

#[test]
fn test_va_arg() {
    let output = c_clang_ir_pliron_ir_exe("va_arg.c");
    assert_eq!(output.status.code(), Some(75));
}

#[test]
fn test_fib() {
    let output = c_clang_ir_pliron_ir_exe("fib.c");
    assert!(output.status.success());
    let fib_output = String::from_utf8(output.stdout).unwrap();
    expect![[r#"
        fib(0): 0
        fib(1): 0
        fib(2): 1
        fib(3): 1
        fib(4): 2
    "#]]
    .assert_eq(&fib_output);
}
