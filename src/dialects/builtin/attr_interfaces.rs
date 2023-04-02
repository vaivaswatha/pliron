use crate::{attribute::Attribute, context::Ptr, r#type::TypeObj};

/// Does [Attribute] have a [Type](crate::type::Type)?
/// This serves the same purpose as MLIR's `TypedAttrInterface`.
pub trait TypedAttrInterface: Attribute {
    /// Get this attribute's type.
    fn get_type(&self) -> Option<Ptr<TypeObj>>;
}
