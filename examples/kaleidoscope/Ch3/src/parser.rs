use std::io::Read;

use crate::ast::{Expr, Function, Operator, Program, Prototype};
use crate::error::{Error, Result};
use crate::lexer::Lexer;
use crate::token::Token;

pub struct Parser<R: Read> {
    lexer: Lexer<R>,
}

impl<R: Read> Parser<R> {
    pub fn new(lexer: Lexer<R>) -> Self {
        Self { lexer }
    }

    pub fn parse(&mut self) -> Result<Program> {
        let mut functions = vec![];
        let mut externs = vec![];
        let mut main = vec![];

        loop {
            let (token, _) = self.lexer.peek_token()?;
            match token {
                Token::Eof => break,
                Token::SemiColon => {
                    self.lexer.next_token()?;
                    continue;
                }
                Token::Def => functions.push(self.parse_definition()?),
                Token::Extern => externs.push(self.parse_extern()?),
                _ => main.push(self.parse_top_level_expr()?),
            }
        }
        Ok(Program {
            functions,
            externs,
            main,
        })
    }

    fn parse_definition(&mut self) -> Result<Function> {
        self.tok(Token::Def)?;
        let prototype = self.prototype()?;
        let body = self.expr()?;
        Ok(Function { prototype, body })
    }

    fn parse_extern(&mut self) -> Result<Prototype> {
        self.tok(Token::Extern)?;
        self.prototype()
    }

    fn prototype(&mut self) -> Result<Prototype> {
        let name = self.ident()?;
        let args = self.parameters()?;
        Ok(Prototype { name, args })
    }

    fn parameters(&mut self) -> Result<Vec<String>> {
        self.tok(Token::OpenParen)?;
        let mut params = vec![];
        loop {
            let (tok, loc) = self.lexer.next_token()?;
            match tok {
                Token::Identifier(s) => params.push(s),
                Token::CloseParen => break,
                token => return Err(Error::Unexpected(loc, Token::CloseParen, token)),
            }
        }
        Ok(params)
    }

    fn parse_top_level_expr(&mut self) -> Result<Expr> {
        self.expr()
    }

    fn expr(&mut self) -> Result<Expr> {
        self.expr_climbing(10)
    }

    fn expr_climbing(self: &mut Self, min_prec: usize) -> Result<Expr> {
        let mut res = self.primary()?;
        while let Some(op) = self.peek_operator()? {
            let next_prec = op_precendence(op);
            if next_prec <= min_prec {
                break;
            }
            self.lexer.next_token()?;
            let rhs = self.expr_climbing(next_prec)?;

            res = Expr::Binary {
                op,
                lhs: Box::new(res),
                rhs: Box::new(rhs),
            };
        }
        Ok(res)
    }

    fn peek_operator(&mut self) -> Result<Option<Operator>> {
        let (tok, _) = self.lexer.peek_token()?;
        let res = match tok {
            Token::LessThan => Some(Operator::LessThan),
            Token::Minus => Some(Operator::Minus),
            Token::Plus => Some(Operator::Plus),
            Token::Star => Some(Operator::Times),
            _ => None,
        };
        Ok(res)
    }

    fn primary(&mut self) -> Result<Expr> {
        let (tok, loc) = self.lexer.next_token()?;
        match tok {
            Token::Identifier(s) => {
                let (tok, _) = self.lexer.peek_token()?;
                if tok == &Token::OpenParen {
                    self.fncall(s)
                } else {
                    Ok(Expr::Variable(s))
                }
            }
            Token::Number(n) => Ok(Expr::Number(n)),
            Token::OpenParen => {
                let e = self.expr()?;
                self.tok(Token::CloseParen)?;
                Ok(e)
            }
            token => Err(Error::Unexpected(loc, Token::Identifier("".into()), token)),
        }
    }

    fn fncall(&mut self, name: String) -> Result<Expr> {
        let args = self.args()?;
        Ok(Expr::Call { name, args })
    }

    fn args(&mut self) -> Result<Vec<Expr>> {
        self.tok(Token::OpenParen)?;
        if self.peek_tok(Token::CloseParen)? {
            self.lexer.next_token().unwrap();
            return Ok(vec![]);
        }

        let mut args = vec![self.expr()?];
        while self.peek_tok(Token::Comma)? {
            self.lexer.next_token().unwrap();
            args.push(self.expr()?);
        }
        self.tok(Token::CloseParen)?;
        Ok(args)
    }

    fn ident(&mut self) -> Result<String> {
        let (tok, loc) = self.lexer.next_token()?;
        match tok {
            Token::Identifier(s) => Ok(s),
            token => Err(Error::Unexpected(loc, Token::Identifier("".into()), token)),
        }
    }

    fn tok(&mut self, expected: Token) -> Result<()> {
        let (token, loc) = self.lexer.next_token()?;
        if token == expected {
            Ok(())
        } else {
            Err(Error::Unexpected(loc, expected, token))
        }
    }

    fn peek_tok(&mut self, expected: Token) -> Result<bool> {
        let (token, _) = self.lexer.peek_token()?;
        Ok(token == &expected)
    }
}

fn op_precendence(op: Operator) -> usize {
    match op {
        Operator::LessThan => 10,
        Operator::Minus => 20,
        Operator::Plus => 20,
        Operator::Times => 40,
    }
}
