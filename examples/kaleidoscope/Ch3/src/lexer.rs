use std::{
    io::{Bytes, Read},
    iter::Peekable,
};

use thiserror::Error;

use crate::error::Result;
use crate::token::Token;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Unexpected character: {0}")]
    UnexpectedChar(char),
    #[error("Invalid number: {0}")]
    InvalidNumber(#[from] std::num::ParseFloatError),
}

pub struct Lexer<R: Read> {
    bytes: Peekable<Bytes<R>>,
    lexed: Option<(Token, Location)>,
    loc: Location,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Location {
    pub line: usize,
    pub column: usize,
    pub offset: usize,
}

impl Location {
    pub fn new() -> Self {
        Self {
            line: 1,
            column: 1,
            offset: 0,
        }
    }

    pub fn advance(&mut self, c: char) {
        self.offset += 1;
        self.column += 1;
        if c == '\n' {
            self.line += 1;
            self.column = 1;
        }
    }
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

const KW_DEF: &str = "def";
const KW_EXTERN: &str = "extern";

impl<R: Read> Lexer<R> {
    pub fn new(reader: R) -> Self {
        Self {
            bytes: reader.bytes().peekable(),
            lexed: None,
            loc: Location::new(),
        }
    }

    pub fn peek_token(&mut self) -> Result<&(Token, Location)> {
        match self.lexed {
            Some(ref token) => Ok(token),
            None => {
                self.lexed = Some(self.next_token()?);
                self.peek_token()
            }
        }
    }

    pub fn next_token(&mut self) -> Result<(Token, Location)> {
        if let Some(token) = self.lexed.take() {
            return Ok(token);
        }

        loop {
            let Some(b) = self.peek()? else {
                return Ok((Token::Eof, self.loc.clone()));
            };

            // Skip whitespace and comments
            match b {
                '#' => {
                    self.comment()?;
                    continue;
                }
                _ if b.is_ascii_whitespace() => {
                    self.next();
                    continue;
                }
                _ => (),
            }

            let loc = self.loc.clone();
            let tok = match b {
                'a'..='z' | 'A'..='Z' => self.identifier()?,
                '0'..='9' | '.' => self.number()?,
                _ => {
                    self.next();
                    match b {
                        '+' => Token::Plus,
                        '-' => Token::Minus,
                        '*' => Token::Star,
                        '<' => Token::LessThan,
                        ';' => Token::SemiColon,
                        '(' => Token::OpenParen,
                        ')' => Token::CloseParen,
                        ',' => Token::Comma,
                        _ => Err(Error::UnexpectedChar(b))?,
                    }
                }
            };
            return Ok((tok, loc));
        }
    }

    fn comment(&mut self) -> Result<()> {
        while let Some(b) = self.peek()? {
            if b == '\n' {
                break;
            }
            self.next();
        }
        Ok(())
    }

    fn identifier(&mut self) -> Result<Token> {
        let mut identifier = String::new();
        while let Some(b) = self.peek()? {
            if b.is_ascii_alphanumeric() {
                identifier.push(b as char);
                self.next();
            } else {
                break;
            }
        }
        Ok(match identifier.as_str() {
            KW_DEF => Token::Def,
            KW_EXTERN => Token::Extern,
            _ => Token::Identifier(identifier),
        })
    }

    fn number(&mut self) -> Result<Token> {
        let mut buf = String::new();
        self.digits(&mut buf)?;
        if let Some('.') = self.peek()? {
            buf.push('.');
            self.next();
            self.digits(&mut buf)?;
        }
        Ok(Token::Number(buf.parse().map_err(Error::InvalidNumber)?))
    }

    fn digits(&mut self, buf: &mut String) -> Result<()> {
        while let Some(b) = self.peek()? {
            if b.is_ascii_digit() {
                buf.push(b as char);
                self.next();
            } else {
                break;
            }
        }
        Ok(())
    }

    fn peek(&mut self) -> Result<Option<char>> {
        if let Some(&Ok(byte)) = self.bytes.peek() {
            return Ok(Some(byte as char));
        };
        match self.bytes.next() {
            Some(Ok(_)) => unreachable!(),
            Some(Err(err)) => Err(err.into()),
            None => Ok(None),
        }
    }

    fn next(&mut self) {
        match self.bytes.next() {
            Some(Ok(b)) => self.loc.advance(b as char),
            Some(Err(err)) => panic!("Error: {}", err),
            None => panic!("Unexpected EOF"),
        }
    }
}
