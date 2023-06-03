//! Utilities for error handling

use std::fmt::Display;

/// The kinds of errors we have during compilation.
#[derive(Debug)]
pub enum CompilerError {
    BadInput { msg: String },
    VerificationError { msg: String },
}

impl Display for CompilerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompilerError::BadInput { msg } => {
                write!(f, "Compilation failed.\n{}", msg)
            }
            CompilerError::VerificationError { msg } => {
                write!(f, "Internal compiler error. Verification failed.\n{}", msg)
            }
        }
    }
}
