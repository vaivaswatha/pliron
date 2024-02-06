use std::{
    fs::File,
    io::{self, BufReader},
    path::Path,
};

use clap::Parser;

mod ast;
mod error;
mod lexer;
mod parser;
mod token;

use lexer::Lexer;

use error::Result;

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

    let mut parser = parser::Parser::new(lexer);
    let program = parser.parse()?;
    println!("{:#?}", program);
    Ok(())
}
