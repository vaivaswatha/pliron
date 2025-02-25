//! Tests that compile code and run it.

use std::{path::PathBuf, sync::LazyLock};

use assert_cmd::Command;
use expect_test::expect;
use pliron::{
    arg_error_noloc, builtin,
    common_traits::Verify,
    context::Context,
    location,
    op::Op,
    operation::Operation,
    parsable::{self, Parsable, state_stream_from_file},
    printable::Printable,
    result::Result,
};
use pliron_llvm::{
    from_llvm_ir,
    llvm_sys::core::{LLVMContext, LLVMModule},
    to_llvm_ir,
};
use tempfile::{TempDir, tempdir};

const CLANG_BINARY: &str = "clang-18";
const LLI_BINARY: &str = "lli-18";

static RESOURCES_DIR: LazyLock<PathBuf> = LazyLock::new(|| {
    [env!("CARGO_MANIFEST_DIR"), "tests", "resources"]
        .iter()
        .collect()
});

// Test Fibonacci code present in `input_file`, which contains fibonacci IR / Bitcode.
fn test_fib(tmp_dir: &TempDir, input_file: &str) {
    // llvm-opt -S -i $tmp/fib.bc -o $tmp/fib.opt.ll
    let mut cmd = Command::cargo_bin("llvm-opt").unwrap();
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
    let mut cmd = Command::new(CLANG_BINARY);
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
    let mut cmd = Command::new(CLANG_BINARY);
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

/// Test Fibonacci by reading in fib.mem2reg.ll
#[test]
fn test_fib_after_mem2reg() {
    // Create a tempdir() to place the temporary compiled files.
    let tmp_dir = tempdir().unwrap();
    test_fib(&tmp_dir, "fib.mem2reg.ll")
}

pub fn setup_context_dialects() -> Context {
    let mut ctx = Context::new();
    builtin::register(&mut ctx);
    pliron_llvm::register(&mut ctx);

    ctx
}

/// Test Fibonacci by reading in pliron's llvm-dialect IR.
fn test_fib_plir(filename: &str) -> Result<()> {
    let ctx = &mut setup_context_dialects();
    let llvm_context = LLVMContext::default();

    let fib_mem2reg_ll_path = RESOURCES_DIR.join(filename);
    let module = LLVMModule::from_ir_in_file(&llvm_context, fib_mem2reg_ll_path.to_str().unwrap())
        .map_err(|err| arg_error_noloc!("{}", err))?;
    let pliron_module = from_llvm_ir::convert_module(ctx, &module)?;
    pliron_module.get_operation().verify(ctx)?;

    // Create a temp dir to place the plir file.
    let tmp_dir = tempdir().unwrap();
    let fib_mem2reg_plir_path = tmp_dir.path().join(filename);
    // Write the plir to a file.
    std::fs::write(
        fib_mem2reg_plir_path.clone(),
        pliron_module.disp(ctx).to_string(),
    )
    .map_err(|e| arg_error_noloc!(e))?;

    // println!("plir file created:\n{}", std::fs::read_to_string(&fib_mem2reg_plir_path).unwrap());

    // Now parse the plir file and verify it.
    let fib_mem2reg_plir = std::fs::File::open(&fib_mem2reg_plir_path).unwrap();
    let mut fib_mem2reg_plir = std::io::BufReader::new(fib_mem2reg_plir);

    let source = location::Source::new_from_file(ctx, fib_mem2reg_plir_path);
    let state_stream =
        state_stream_from_file(&mut fib_mem2reg_plir, parsable::State::new(ctx, source));

    let parsed_res = match Operation::parser(()).parse(state_stream) {
        Ok((parsed_res, _)) => parsed_res,
        Err(err) => {
            eprintln!("{}", err);
            panic!("Error parsing {}", filename);
        }
    };

    match parsed_res.verify(ctx) {
        Ok(_) => Ok(()),
        Err(err) => {
            eprintln!("{}", err.disp(ctx));
            panic!("Error verifying {}", filename);
        }
    }
}

#[test]
fn test_fib_plir_mem2reg() -> Result<()> {
    test_fib_plir("fib.mem2reg.ll")
}

#[test]
fn test_fib_plir_noopt() -> Result<()> {
    test_fib_plir("fib.ll")
}

/// Test an LLVM-IR file by executing it and comparing the output.
/// The input file is `input_file`, which contains LLVM IR / Bitcode.
/// The expected output is `expected_output`.
fn test_llvm_ir_via_pliron(input_file: &str, expected_output: i32) {
    let llvm_context = LLVMContext::default();
    let module = LLVMModule::from_ir_in_file(&llvm_context, input_file)
        .map_err(|err| arg_error_noloc!("{}", err))
        .unwrap();
    let ctx = &mut setup_context_dialects();
    let pliron_module = from_llvm_ir::convert_module(ctx, &module)
        .map_err(|err| arg_error_noloc!("{}", err))
        .unwrap();

    match pliron_module.get_operation().verify(ctx) {
        Ok(_) => (),
        Err(err) => {
            eprintln!("{}", err.disp(ctx));
            panic!("Error verifying {}", input_file);
        }
    }

    // Write the plir to a file.
    let tmp_dir = tempdir().unwrap();
    let plir_path = tmp_dir.path().join("output.plir");
    // Write the plir to a file.
    std::fs::write(plir_path.clone(), pliron_module.disp(ctx).to_string())
        .map_err(|e| arg_error_noloc!(e))
        .unwrap();

    println!(
        "plir file created:\n{}",
        std::fs::read_to_string(&plir_path).unwrap()
    );

    // Parse the plir file and verify it.
    let plir_file = std::fs::File::open(&plir_path).unwrap();
    let mut plir_file = std::io::BufReader::new(plir_file);

    let source = location::Source::new_from_file(ctx, plir_path.clone());
    let state_stream = state_stream_from_file(&mut plir_file, parsable::State::new(ctx, source));

    let parsed_res = match Operation::parser(()).parse(state_stream) {
        Ok((parsed_res, _)) => parsed_res,
        Err(err) => {
            eprintln!("{}", err);
            panic!("Error parsing {}", plir_path.to_str().unwrap());
        }
    };

    match parsed_res.verify(ctx) {
        Ok(_) => (),
        Err(err) => {
            eprintln!("{}", err.disp(ctx));
            panic!("Error verifying {}", plir_path.to_str().unwrap());
        }
    }

    // Execute it and try.
    let module = to_llvm_ir::convert_module(ctx, &llvm_context, pliron_module)
        .map_err(|err| arg_error_noloc!("{}", err))
        .unwrap();
    module
        .verify()
        .map_err(|err| arg_error_noloc!("{}", err.to_string()))
        .unwrap();

    // Write the bitcode to a file.
    let bc_path = tmp_dir.path().join("output.bc");
    module
        .bitcode_to_file(bc_path.to_str().unwrap())
        .map_err(|_err| arg_error_noloc!("{}", "Error writing bitcode to file"))
        .unwrap();

    let mut cmd = Command::new(LLI_BINARY);

    let run_output = cmd
        .current_dir(&*RESOURCES_DIR)
        .args([bc_path.to_str().unwrap()])
        .output()
        .expect("failed to execute LLi to execute output.bc");
    assert_eq!(
        run_output.status.code(),
        Some(expected_output),
        "{}",
        String::from_utf8(run_output.stderr).unwrap()
    );
}

/// Test simple-loop by compiling simple-loop.ll via pliron.
#[test]
fn test_simple_loop_via_pliron() {
    test_llvm_ir_via_pliron(RESOURCES_DIR.join("simple-loop.ll").to_str().unwrap(), 15);
}

/// Test insert_extract_value by compiling insert_extract_value.ll via pliron.
#[test]
fn test_insert_extract_value_via_pliron() {
    test_llvm_ir_via_pliron(
        RESOURCES_DIR
            .join("insert_extract_value.ll")
            .to_str()
            .unwrap(),
        103,
    );
}
