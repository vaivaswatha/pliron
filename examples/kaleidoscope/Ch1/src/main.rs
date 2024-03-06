use std::{
    fs::File,
    io::{self, BufReader},
    path::Path,
};

use clap::Parser;
use lexer::Lexer;

mod error;
mod lexer;
mod token;

use error::Result;

use crate::token::Token;

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

    let mut lexer = Lexer::new(&mut reader);
    loop {
        let token = lexer.next_token()?;
        if token == Token::Eof {
            break;
        }
        println!("{:?}", token);
    }

    Ok(())
}
