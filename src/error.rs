//! Utilities for error handling

use thiserror::Error;

use crate::dialect_conversion::ConversionError;

/// The kinds of errors we have during compilation.
#[derive(Debug, Error)]
pub enum CompilerError {
    #[error("Compilation failed: {msg}")]
    BadInput { msg: String },
    #[error("Internal compiler error. Verification failed: {msg}")]
    VerificationError { msg: String },
    #[error("Internal compiler error. Conversion failed: {0}")]
    ConversionError(#[from] ConversionError),
}
