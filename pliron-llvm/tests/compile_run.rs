//! Tests that compile code and run it.

use std::{env, path::PathBuf, sync::LazyLock};

mod common;
use combine::Parser;
use common::init_env_logger;

use assert_cmd::Command;
use pliron::{
    arg_error_noloc, builtin,
    common_traits::Verify,
    context::Context,
    location,
    op::Op,
    operation::Operation,
    parsable::{self, state_stream_from_file},
    printable::Printable,
};
use pliron_llvm::{
    from_llvm_ir,
    llvm_sys::core::{LLVMContext, LLVMModule, llvm_print_module_to_string},
    to_llvm_ir,
};
use tempfile::tempdir;

const LLI_BINARY: &str = "lli-20";

static RESOURCES_DIR: LazyLock<PathBuf> = LazyLock::new(|| {
    [env!("CARGO_MANIFEST_DIR"), "tests", "resources"]
        .iter()
        .collect()
});

pub fn setup_context_dialects() -> Context {
    let mut ctx = Context::new();
    builtin::register(&mut ctx);
    pliron_llvm::register(&mut ctx);

    ctx
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
    let pliron_module = match from_llvm_ir::convert_module(ctx, &module) {
        Ok(plir) => plir,
        Err(err) => {
            eprintln!("{}", err.disp(ctx));
            panic!("Error converting {input_file}");
        }
    };

    log::debug!(
        "pliron module constructed from input LLVM-IR:\n{}",
        pliron_module.disp(ctx)
    );

    match pliron_module.get_operation().verify(ctx) {
        Ok(_) => (),
        Err(err) => {
            eprintln!("{}", err.disp(ctx));
            panic!("Error verifying {input_file}");
        }
    }

    // Write the plir to a file.
    let tmp_dir = tempdir().unwrap();
    let plir_path = tmp_dir.path().join("output.plir");
    // Write the plir to a file.
    std::fs::write(plir_path.clone(), pliron_module.disp(ctx).to_string())
        .map_err(|e| arg_error_noloc!(e))
        .unwrap();

    // Parse the plir file and verify it.
    let plir_file = std::fs::File::open(&plir_path).unwrap();
    let mut plir_file = std::io::BufReader::new(plir_file);

    let source = location::Source::new_from_file(ctx, plir_path.clone());
    let state_stream = state_stream_from_file(&mut plir_file, parsable::State::new(ctx, source));

    let parsed_res = match Operation::top_level_parser().parse(state_stream) {
        Ok((parsed_res, _)) => parsed_res,
        Err(err) => {
            eprintln!("{err}");
            panic!("Error parsing {}", plir_path.to_str().unwrap());
        }
    };

    log::debug!(
        "pliron module re-parsed after printing:\n{}",
        parsed_res.disp(ctx)
    );

    match parsed_res.verify(ctx) {
        Ok(_) => (),
        Err(err) => {
            eprintln!("{}", err.disp(ctx));
            panic!("Error verifying {}", plir_path.to_str().unwrap());
        }
    }

    // Execute it and try.
    let module = match to_llvm_ir::convert_module(ctx, &llvm_context, pliron_module) {
        Ok(module) => module,
        Err(err) => {
            eprintln!("{}", err.disp(ctx));
            panic!("Error converting {}", plir_path.to_str().unwrap());
        }
    };

    log::debug!(
        "LLVM module generated from pliron LLVM-IR:\n{}",
        llvm_print_module_to_string(&module).unwrap()
    );

    match module.verify() {
        Ok(_) => (),
        Err(err) => {
            eprintln!("{err}");
            panic!("Error verifying {}", plir_path.to_str().unwrap());
        }
    }

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
fn test_simple_loop() {
    init_env_logger();
    test_llvm_ir_via_pliron(RESOURCES_DIR.join("simple-loop.ll").to_str().unwrap(), 15);
}

/// Test insert_extract_value by compiling insert_extract_value.ll via pliron.
#[test]
fn test_insert_extract_value() {
    init_env_logger();
    test_llvm_ir_via_pliron(
        RESOURCES_DIR
            .join("insert_extract_value.ll")
            .to_str()
            .unwrap(),
        103,
    );
}

/// Test SelectOp by compiling select.ll via pliron.
#[test]
fn test_select() {
    init_env_logger();
    test_llvm_ir_via_pliron(RESOURCES_DIR.join("select.ll").to_str().unwrap(), 100);
}

/// Test const structs and arrays
#[test]
fn test_consts() {
    init_env_logger();
    test_llvm_ir_via_pliron(RESOURCES_DIR.join("consts.ll").to_str().unwrap(), 203);
}

/// Test globals
#[test]
fn test_globals() {
    init_env_logger();
    test_llvm_ir_via_pliron(RESOURCES_DIR.join("globals.ll").to_str().unwrap(), 59);
}

/// Test fib by compiling fib.ll via pliron.
#[test]
fn test_fib() {
    init_env_logger();
    test_llvm_ir_via_pliron(RESOURCES_DIR.join("fib.ll").to_str().unwrap(), 3);
}

/// Test fib.mem2reg by compiling fib.ll via pliron.
#[test]
fn test_fib_mem2reg() {
    init_env_logger();
    test_llvm_ir_via_pliron(RESOURCES_DIR.join("fib.mem2reg.ll").to_str().unwrap(), 5);
}
