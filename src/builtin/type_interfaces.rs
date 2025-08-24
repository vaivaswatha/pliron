use crate::{context::Context, result::Result, r#type::Type, utils::apfloat::Semantics};
use pliron_derive::type_interface;

#[type_interface]
pub trait FloatType {
    fn get_semantics(&self) -> Semantics;
    fn verify(_attr: &dyn Type, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}
