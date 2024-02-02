#[derive(Debug, PartialEq)]
pub enum Token {
    Eof,

    // Commands.
    Def,
    Extern,

    // Primary.
    Identifier(String),
    Number(f64),

    // Operators.
    LessThan,
    Minus,
    Plus,
    Star,

    // Other.
    SemiColon,
    OpenParen,
    CloseParen,
    Comma,
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Token::Eof => write!(f, "EOF"),

            // Commands.
            Token::Def => write!(f, "def"),
            Token::Extern => write!(f, "extern"),

            // Primary.
            Token::Identifier(s) => write!(f, "{}", s),
            Token::Number(n) => write!(f, "{}", n),

            // Operators.
            Token::LessThan => write!(f, "<"),
            Token::Minus => write!(f, "-"),
            Token::Plus => write!(f, "+"),
            Token::Star => write!(f, "*"),

            // Other.
            Token::SemiColon => write!(f, ";"),
            Token::OpenParen => write!(f, "("),
            Token::CloseParen => write!(f, ")"),
            Token::Comma => write!(f, ","),
        }
    }
}
