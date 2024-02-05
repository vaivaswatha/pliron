use std::io;

use thiserror::Error;

use crate::{
    lexer::{self, Location},
    token::Token,
};

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Io(#[from] io::Error),

    #[error(transparent)]
    Lexer(#[from] lexer::Error),

    #[error("Expected {1}, got {2} at {0}")]
    Unexpected(Location, Token, Token),

    #[error("Expected identifier, got {1} at {0}")]
    ExpectedIdentifier(Location, Token),

    #[error("variable {0} not found")]
    VariableNotFound(String),
}

pub type Result<T> = std::result::Result<T, Error>;
