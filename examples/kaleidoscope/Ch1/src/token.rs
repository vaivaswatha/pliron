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
