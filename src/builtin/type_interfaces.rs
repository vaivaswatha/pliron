use crate::{context::Context, result::Result, r#type::Type, utils::apfloat::Semantics};
use pliron_derive::type_interface;

#[type_interface]
pub trait FloatType {
    /// Returns the semantics of the float type.
    fn get_semantics(&self) -> Semantics;
    fn verify(_attr: &dyn Type, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}
