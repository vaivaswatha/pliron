#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    pub functions: Vec<Function>,
    pub externs: Vec<Prototype>,
    pub main: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Number(f64),
    Variable(String),
    Binary {
        op: Operator,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Call {
        name: String,
        args: Vec<Expr>,
    },
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum Operator {
    LessThan,
    Minus,
    Plus,
    Times,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Prototype {
    pub name: String,
    pub args: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub prototype: Prototype,
    pub body: Expr,
}
