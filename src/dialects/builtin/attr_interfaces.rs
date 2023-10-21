use crate::{
    attribute::Attribute,
    context::{Context, Ptr},
    error::Result,
    r#type::TypeObj,
};

/// [Attribute]s that have an associated [Type](crate::type::Type).
/// This serves the same purpose as MLIR's `TypedAttrInterface`.
pub trait TypedAttrInterface: Attribute {
    /// Get this attribute's type.
    fn get_type(&self) -> Ptr<TypeObj>;

    fn verify(_attr: &dyn Attribute, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}
