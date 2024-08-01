use std::{path::PathBuf, process::ExitCode};

use clap::Parser;
use pliron::{
    arg_error_noloc, context::Context, printable::Printable, result::Result, verify_error_noloc,
};
use pliron_llvm::{
    from_llvm_ir,
    llvm_sys::core::{llvm_context_create, LLVMModule},
    to_llvm_ir,
};

#[derive(Parser)]
#[command(version, about="LLVM Optimizer", long_about = None)]
struct Cli {
    /// Input LLVM IR (text) / Bitcode file
    #[arg(
        short,
        value_name = "FILE",
        long_help = "Filenames with .ll extension implies textual LLVM-IR. \
                     Otherwise bitcode is assumed."
    )]
    input: PathBuf,

    /// Output LLVM file
    #[arg(short, value_name = "FILE")]
    output: PathBuf,

    /// Emit text LLVM-IR
    #[arg(short = 'S', default_value_t = false)]
    text_output: bool,
}

fn run(cli: Cli, ctx: &mut Context) -> Result<()> {
    let llvm_context = llvm_context_create();
    let is_text_ir = cli.input.extension().filter(|ext| *ext == "ll").is_some();
    let module = if is_text_ir {
        LLVMModule::from_ir_in_file(llvm_context, cli.input.to_str().unwrap())
    } else {
        LLVMModule::from_bitcode_in_file(llvm_context, cli.input.to_str().unwrap())
    }
    .map_err(|err| arg_error_noloc!("{}", err))?;

    let pliron_module = from_llvm_ir::convert_module(ctx, &module)?;
    println!("{}", pliron_module.disp(ctx));

    let module = to_llvm_ir::convert_module(ctx, llvm_context, pliron_module)?;
    module
        .verify()
        .map_err(|err| verify_error_noloc!("{}", err.to_string()))?;

    if cli.text_output {
        module
            .to_ir_file(cli.output.to_str().unwrap())
            .map_err(|err| arg_error_noloc!("{}", err.to_string()))?;
    } else {
        module
            .to_bitcode_file(cli.output.to_str().unwrap())
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
