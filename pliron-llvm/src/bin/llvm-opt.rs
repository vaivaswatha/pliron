use std::{path::PathBuf, process::ExitCode};

use inkwell::{context::Context as IWContext, module::Module as IWModule};

use clap::Parser;
use pliron::{arg_error_noloc, context::Context, printable::Printable, result::Result};
use pliron_llvm::from_inkwell;

#[derive(Parser)]
#[command(version, about="LLVM Optimizer", long_about = None)]
struct Cli {
    /// Input LLVM file
    #[arg(short, value_name = "FILE")]
    input: PathBuf,

    /// Output LLVM file
    #[arg(short, value_name = "FILE")]
    output: PathBuf,

    /// Emit text LLVM-IR
    #[arg(short = 'S', default_value_t = false)]
    text_output: bool,
}

fn run(cli: Cli, ctx: &mut Context) -> Result<()> {
    let context = IWContext::create();
    let module = IWModule::parse_bitcode_from_path(cli.input, &context)
        .map_err(|err| arg_error_noloc!("{}", err))?;

    let pliron_module = from_inkwell::convert_module(ctx, &module)?;
    println!("{}", pliron_module.disp(ctx));

    if cli.text_output {
        module
            .print_to_file(&cli.output)
            .map_err(|err| arg_error_noloc!("{}", err.to_string()))?;
    } else {
        module.write_bitcode_to_path(&cli.output);
    }
    Ok(())
}

pub fn main() -> ExitCode {
    let cli = Cli::parse();
    let ctx = &mut Context::default();
    match run(cli, ctx) {
        Ok(_) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{}", e.disp(ctx));
            ExitCode::FAILURE
        }
    }
}
