use fraction::Fraction;

use pliron::attribute::{AttrObj, Attribute};
use pliron::context::Ptr;
use pliron::dialect::Dialect;
use pliron::dialects::builtin::attr_interfaces::TypedAttrInterface;
use pliron::error::Result;
use pliron::impl_attr_interface;
use pliron::parsable::Parsable;
use pliron::r#type::TypeObj;
use pliron::{common_traits::Verify, context::Context};
use pliron_derive::{def_attribute, NotParsableAttribute, Printable};

pub const ATTR_KEY_CALLEE_NAME: &str = "kal.callee";

pub(super) fn register(dialect: &mut Dialect) {
    BinOpAttr::register_attr_in_dialect(dialect, BinOpAttr::parser_fn);
    NumberAttr::register_attr_in_dialect(dialect, NumberAttr::parser_fn);
    ParamsAttr::register_attr_in_dialect(dialect, ParamsAttr::parser_fn);
}

#[def_attribute]
#[attr_name = "kal.bin_op"]
#[derive(Debug, Clone, PartialEq, Hash, Printable, NotParsableAttribute)]
#[ir_format = "`<` $op `>`"]
pub struct BinOpAttr {
    op: BinaryOperator,
}
impl Verify for BinOpAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl BinOpAttr {
    pub const KEY: &'static str = "kal.bin_op";

    pub fn create(op: BinaryOperator) -> AttrObj {
        Box::new(Self { op })
    }

    pub fn op(&self) -> BinaryOperator {
        self.op
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum BinaryOperator {
    LessThan,
    Minus,
    Plus,
    Times,
}

impl std::fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::LessThan => write!(f, "<"),
            BinaryOperator::Minus => write!(f, "-"),
            BinaryOperator::Plus => write!(f, "+"),
            BinaryOperator::Times => write!(f, "*"),
        }
    }
}

#[def_attribute]
#[attr_name = "kal.number"]
#[derive(Debug, Clone, PartialEq, Hash, Printable, NotParsableAttribute)]
// #[ir_format = "$integral `.` $fractional"]
pub struct NumberAttr {
    num: Fraction,
    ty: Ptr<TypeObj>,
}
impl Verify for NumberAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl_attr_interface!(
    TypedAttrInterface for NumberAttr {
        fn get_type(&self) -> Ptr<TypeObj> {
            self.ty
        }
    }
);
impl NumberAttr {
    pub fn create(n: f64, ty: Ptr<TypeObj>) -> AttrObj {
        let x = Box::new(Self {
            num: Fraction::from(n),
            ty,
        });
        x
    }
}

#[def_attribute]
#[attr_name = "kal.params"]
#[derive(Debug, Clone, PartialEq, Hash, Printable, NotParsableAttribute)]
#[ir_format = "`(` $params `)`"]
pub struct ParamsAttr {
    params: Vec<String>,
}
impl Verify for ParamsAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl ParamsAttr {
    pub const KEY: &'static str = "kal.params";

    pub fn create(params: Vec<String>) -> AttrObj {
        Box::new(Self { params })
    }

    pub fn params(&self) -> Vec<String> {
        self.params.clone()
    }
}
