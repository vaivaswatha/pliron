use std::io;

use thiserror::Error;

use crate::lexer;

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Io(#[from] io::Error),

    #[error(transparent)]
    Lexer(#[from] lexer::Error),
}

pub type Result<T> = std::result::Result<T, Error>;
