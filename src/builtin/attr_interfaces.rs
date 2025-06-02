use pliron::derive::attr_interface;

use crate::{
    attribute::Attribute,
    context::{Context, Ptr},
    result::Result,
    r#type::TypeObj,
};

/// [Attribute]s that have an associated [Type](crate::type::Type).
/// This serves the same purpose as MLIR's `TypedAttrInterface`.
#[attr_interface]
pub trait TypedAttrInterface {
    /// Get this attribute's type.
    fn get_type(&self) -> Ptr<TypeObj>;

    fn verify(_attr: &dyn Attribute, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

/// [Attribute]s that should be printed after the top level [Operation](crate::operation::Operation)
/// is printed. An [Op](crate::op::Op) may choose to print such an attribute as part of its
/// syntax specification. This will be unknown to the outline attributes printer and will be
/// printed nevertheless while printing all outline attributes.
#[attr_interface]
pub trait OutlinedAttr {
    fn verify(_attr: &dyn Attribute, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

/// [Attribute]s that should be printed only once, and some form of "reference" to be
/// used for repeated printing. These must be outlined attributes.
#[attr_interface]
pub trait PrintOnceAttr: OutlinedAttr {
    fn verify(_attr: &dyn Attribute, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}
