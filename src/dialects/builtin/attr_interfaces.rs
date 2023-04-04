//! Common semantics, API and behaviour of [Attribute]s are
//! abstracted into interfaces.
//!
//! Interfaces in pliron capture MLIR
//! functionality of both [Traits](https://mlir.llvm.org/docs/Traits/)
//! and [Interfaces](https://mlir.llvm.org/docs/Interfaces/).
//!
//! [Attribute]s that implement an interface can choose to annotate
//! the `impl` with [`#[cast_to]`](https://docs.rs/intertrait/latest/intertrait/#usage).
//! This will enable an [AttrObj](crate::attribute::AttrObj) to be [cast](intertrait::cast::CastRef::cast)
//! into an interface object (or check if it [impls](intertrait::cast::CastRef::impls) it).
//! Without this, a cast will always fail.

use crate::{attribute::Attribute, context::Ptr, r#type::TypeObj};

/// [Attribute]s that have an associated [Type](crate::type::Type).
/// This serves the same purpose as MLIR's `TypedAttrInterface`.
pub trait TypedAttrInterface: Attribute {
    /// Get this attribute's type.
    fn get_type(&self) -> Ptr<TypeObj>;
}
