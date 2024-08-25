use std::{path::PathBuf, process::ExitCode};

use clap::Parser;
use pliron::{
    arg_error_noloc, context::Context, printable::Printable, result::Result, verify_error_noloc,
};
use pliron_llvm::{
    from_llvm_ir,
    llvm_sys::core::{LLVMContext, LLVMModule},
    to_llvm_ir,
};

#[derive(Parser)]
#[command(version, about="LLVM Optimizer", long_about = None)]
struct Cli {
    /// Input LLVM-IR (Assembly / Bitcode) file
    #[arg(short, value_name = "FILE")]
    input: PathBuf,

    /// Output LLVM file
    #[arg(short, value_name = "FILE")]
    output: PathBuf,

    /// Emit text assembly LLVM-IR
    #[arg(short = 'S', default_value_t = false)]
    text_output: bool,
}

fn run(cli: Cli, ctx: &mut Context) -> Result<()> {
    let llvm_context = LLVMContext::default();
    let module = LLVMModule::from_ir_in_file(&llvm_context, cli.input.to_str().unwrap())
        .map_err(|err| arg_error_noloc!("{}", err))?;

    let pliron_module = from_llvm_ir::convert_module(ctx, &module)?;
    // pliron_module.get_operation().verify(ctx)?;
    // println!("{}", pliron_module.disp(ctx));

    let module = to_llvm_ir::convert_module(ctx, &llvm_context, pliron_module)?;
    module
        .verify()
        .map_err(|err| verify_error_noloc!("{}", err.to_string()))?;

    if cli.text_output {
        module
            .asm_to_file(cli.output.to_str().unwrap())
            .map_err(|err| arg_error_noloc!("{}", err.to_string()))?;
    } else {
        module
            .bitcode_to_file(cli.output.to_str().unwrap())
            .map_err(|_err| arg_error_noloc!("{}", "Error writing bitcode to file"))?;
    }
    Ok(())
}

pub fn main() -> ExitCode {
    let cli = Cli::parse();
    let ctx = &mut Context::default();
    pliron::builtin::register(ctx);
    pliron_llvm::register(ctx);

    match run(cli, ctx) {
        Ok(_) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{}", e.disp(ctx));
            ExitCode::FAILURE
        }
    }
}
