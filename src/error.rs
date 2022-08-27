use std::fmt::Display;

#[derive(Debug)]
pub enum CompilerError {
    BadInput { msg: String },
    VerificationError { msg: String },
}

impl Display for CompilerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
