use std::{env, path::PathBuf, sync::LazyLock};

use assert_cmd::{Command, cargo::cargo_bin_cmd};
use cargo_manifest::Manifest;
use expect_test::expect;
use tempfile::{TempDir, tempdir};

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

// Test Fibonacci code present in `input_file`, which contains fibonacci IR / Bitcode.
fn test_fib(tmp_dir: &TempDir, input_file: &str) {
    // llvm-opt -S -i $tmp/fib.bc -o $tmp/fib.opt.ll
    let mut cmd = cargo_bin_cmd!();
    let compile_fib = cmd
        .current_dir(&*RESOURCES_DIR)
        .args([
            "-S",
            "-i",
            input_file,
            "-o",
            tmp_dir.path().join("fib.out.ll").to_str().unwrap(),
        ])
        .output()
        .expect("failed to execute llvm-opt to compile fib.bc to fib.out.ll");
    assert!(
        compile_fib.status.success(),
        "{}",
        String::from_utf8(compile_fib.stderr).unwrap()
    );

    // clang -o $tmp/fib $tmp/fib.out.ll tests/resources/fib-main.c
    let mut cmd = Command::new(CLANG_BINARY.clone());
    let compile_fib = cmd
        .current_dir(&*RESOURCES_DIR)
        .args([
            "-o",
            tmp_dir.path().join("fib").to_str().unwrap(),
            tmp_dir.path().join("fib.out.ll").to_str().unwrap(),
            "fib-main.c",
        ])
        .output()
        .expect("failed to execute clang to compile fib-main.c");
    assert!(
        compile_fib.status.success(),
        "{}",
        String::from_utf8(compile_fib.stderr).unwrap()
    );

    // $tmp/fib
    let mut cmd = Command::new(tmp_dir.path().join("fib"));
    let run_fib = cmd.output().expect("Error executing compiled fib program");
    assert!(run_fib.status.success());
    let fib_output = String::from_utf8(run_fib.stdout).unwrap();
    expect![[r#"
        fib(0): 0
        fib(1): 0
        fib(2): 1
        fib(3): 1
        fib(4): 2
    "#]]
    .assert_eq(&fib_output);
}

/// Test Fibonacci by compiling fib.c to bitcode, no optimization.
#[test]
fn test_fib_from_c() {
    // Create a tempdir() to place the temporary compiled files.
    let tmp_dir = tempdir().unwrap();

    // clang -c -emit-llvm -o $tmp/fib.bc tests/resources/fib.c
    let mut cmd = Command::new(CLANG_BINARY.clone());
    let compile_fib = cmd
        .current_dir(&*RESOURCES_DIR)
        .args([
            "-c",
            "-emit-llvm",
            "-o",
            tmp_dir.path().join("fib.bc").to_str().unwrap(),
            "fib.c",
        ])
        .output()
        .expect("failed to execute clang to compile fib.c");
    assert!(
        compile_fib.status.success(),
        "{}",
        String::from_utf8(compile_fib.stderr).unwrap()
    );

    test_fib(&tmp_dir, tmp_dir.path().join("fib.bc").to_str().unwrap())
}
