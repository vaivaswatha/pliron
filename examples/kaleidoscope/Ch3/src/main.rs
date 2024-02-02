use std::{
    fs::File,
    io::{self, BufReader},
    path::Path,
};

use clap::Parser;

mod ast;
mod dialect;
mod error;
mod gen;
mod lexer;
mod parser;
mod token;

use dialect::kal;
use lexer::Lexer;

use error::Result;
use pliron::{context::Context, dialects::builtin, printable::Printable};

/// Simple program to greet a user.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    filename: Option<String>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let mut reader: Box<dyn io::Read> = match args.filename {
        Some(ref filename) => {
            let file = File::open(&Path::new(filename))?;
            Box::new(BufReader::new(file))
        }
        None => Box::new(io::stdin().lock()),
    };

    let lexer = Lexer::new(&mut reader);
    /*
    let mut ctx = Context::new();
    builtin::register(&mut ctx);
    kal::register(&mut ctx);

    let mut parser = parser::Parser::new(&mut ctx, lexer);
    let module = parser.parse()?;
    println!("{}", module.disp(&ctx));
    */

    let mut parser = parser::Parser::new(lexer);
    let program = parser.parse()?;
    println!("{:#?}", program);

    let mut ctx = Context::new();
    builtin::register(&mut ctx);
    kal::register(&mut ctx);
    let module = gen::generate(&mut ctx, program)?;
    println!("{}", module.disp(&ctx));

    Ok(())
}
