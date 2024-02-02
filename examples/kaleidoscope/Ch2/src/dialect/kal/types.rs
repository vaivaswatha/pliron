use pliron::context::Ptr;
use pliron::dialect::Dialect;
use pliron::error::Result;
use pliron::parsable::Parsable;
use pliron::r#type::{Type, TypeObj};
use pliron::{common_traits::Verify, context::Context};
use pliron_derive::{def_type, NotParsableType, Printable};

pub(super) fn register(dialect: &mut Dialect) {
    NumberType::register_type_in_dialect(dialect, NumberType::parser_fn);
    BoolType::register_type_in_dialect(dialect, BoolType::parser_fn);
    UnresolvedType::register_type_in_dialect(dialect, UnresolvedType::parser_fn);
}

#[def_type]
#[type_name = "kal.number"]
#[derive(Debug, Clone, PartialEq, Hash, Printable, NotParsableType)]
pub struct NumberType {}
impl Verify for NumberType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl NumberType {
    pub fn get(ctx: &mut Context) -> Ptr<TypeObj> {
        Type::register_instance(Self {}, ctx)
    }
}

#[def_type]
#[type_name = "kal.bool"]
#[derive(Debug, Clone, PartialEq, Hash, Printable, NotParsableType)]
pub struct BoolType {}
impl Verify for BoolType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl BoolType {
    pub fn get(ctx: &mut Context) -> Ptr<TypeObj> {
        Type::register_instance(Self {}, ctx)
    }
}

#[def_type]
#[type_name = "kal.func"]
#[derive(Debug, Clone, PartialEq, Hash, Printable, NotParsableType)]
pub struct FuncType {
    num_args: usize,
}
impl Verify for FuncType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

#[def_type]
#[type_name = "kal.unresolved_type"]
#[derive(Debug, Clone, PartialEq, Hash, Printable, NotParsableType)]
pub struct UnresolvedType {}
impl Verify for UnresolvedType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl UnresolvedType {
    pub fn get(ctx: &mut Context) -> Ptr<TypeObj> {
        Type::register_instance(Self {}, ctx)
    }
}
