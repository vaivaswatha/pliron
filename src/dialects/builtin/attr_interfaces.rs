use crate::{attribute::Attribute, context::Ptr, r#type::TypeObj};

/// [Attribute]s that have an associated [Type](crate::type::Type).
/// This serves the same purpose as MLIR's `TypedAttrInterface`.
pub trait TypedAttrInterface: Attribute {
    /// Get this attribute's type.
    fn get_type(&self) -> Ptr<TypeObj>;
}
