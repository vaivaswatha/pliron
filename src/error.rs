use std::fmt::Display;

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
