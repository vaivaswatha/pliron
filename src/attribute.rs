//! Attributes are non-SSA data stored in [Operation](crate::operation::Operation)s.
//!
//! See [MLIR Attributes](https://mlir.llvm.org/docs/LangRef/#attributes).
//! Unlike in MLIR, we do not unique attributes, and hence they are mutable.
//! These are similar in concept to [Properties](https://discourse.llvm.org/t/rfc-introducing-mlir-operation-properties/67846).
//! Attribute objects are heavy, boxed, and not wrapped with [Ptr](crate::context::Ptr).
//! They may or may not be clonable. See [clone].

use std::{hash::Hash, ops::Deref};

use downcast_rs::{impl_downcast, Downcast};
use intertrait::CastFrom;

use crate::{
    common_traits::{DisplayWithContext, Verify},
    context::Context,
    dialect::{Dialect, DialectName},
    with_context::AttachContext,
};

/// Basic functionality that every attribute in the IR must implement.
///
/// [AttrObj]s can be downcasted to their concrete types using
/// [downcast_rs](https://docs.rs/downcast-rs/1.2.0/downcast_rs/index.html#example-without-generics).
///
/// [AttrObj]s can be casted into interface objects using
/// [cast](intertrait::cast). A concrete Attribute that `impl`s
/// an interface must use [cast_to](https://docs.rs/intertrait/latest/intertrait/#usage),
/// allowing an [AttrObj] to be cast to that interface object.
pub trait Attribute: DisplayWithContext + Verify + Downcast + CastFrom {
    /// Is self equal to an other Attribute?
    fn eq_attr(&self, other: &dyn Attribute) -> bool;

    /// Get an [Attribute]'s static name. This is *not* per instantnce.
    /// It is mostly useful for printing and parsing the attribute.
    fn get_attr_id(&self) -> AttrId;

    /// Same as [get_attr_id](Self::get_attr_id), but without the self reference.
    fn get_attr_id_static() -> AttrId
    where
        Self: Sized;

    /// Register this attribute's [AttrId] in the dialect it belongs to.
    /// **Warning**: No check is made as to whether this attr is already registered
    ///  in `dialect`.
    fn register_attr_in_dialect(dialect: &mut Dialect)
    where
        Self: Sized,
    {
        dialect.add_attr(Self::get_attr_id_static());
    }
}
impl_downcast!(Attribute);

/// [Attribute] objects are boxed and stored in the IR.
pub type AttrObj = Box<dyn Attribute>;

impl PartialEq for AttrObj {
    fn eq(&self, other: &Self) -> bool {
        (**self).eq_attr(&**other)
    }
}

impl Eq for AttrObj {}

/// Clone clonable attributes.
/// ```
///     # use pliron::{attribute, dialects::builtin::
///     #    {types::{IntegerType, Signedness}, attributes::IntegerAttr}, context::Context};
///     # use apint::ApInt;
///     # let mut ctx = Context::new();
///     let i64_ty = IntegerType::get(&mut ctx, 32, Signedness::Signed);
///     let int64 = IntegerAttr::create(i64_ty, ApInt::from_i64(0));
///     let int64_clone = attribute::clone::<IntegerAttr>(&int64);
///     assert!(int64 == int64_clone);
/// ```
pub fn clone<T: Clone + Attribute>(source: &AttrObj) -> AttrObj {
    Box::new(source.downcast_ref::<T>().unwrap().clone())
}

impl AttachContext for AttrObj {}
impl DisplayWithContext for AttrObj {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.as_ref().fmt(ctx, f)
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
/// An [Attribute]'s name (not including it's dialect).
pub struct AttrName(String);

impl AttrName {
    /// Create a new AttrName.
    pub fn new(name: &str) -> AttrName {
        AttrName(name.to_string())
    }
}

impl AttachContext for AttrName {}
impl DisplayWithContext for AttrName {
    fn fmt(&self, _ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Deref for AttrName {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
/// A combination of a Attr's name and its dialect.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct AttrId {
    pub dialect: DialectName,
    pub name: AttrName,
}

impl AttachContext for AttrId {}
impl DisplayWithContext for AttrId {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{}.{}",
            self.dialect.with_ctx(ctx),
            self.name.with_ctx(ctx)
        )
    }
}

/// impl [Attribute] for a rust type with boilerplate code.
///
/// Usage:
/// ```
/// #[derive(PartialEq, Eq, Hash)]
/// struct MyAttr { }
/// impl_attr!(
///     /// MyAttr is mine
///     MyAttr,
///     "name",
///     "dialect"
/// );
/// # use pliron::{
/// #     impl_attr, with_context::AttachContext, common_traits::DisplayWithContext,
/// #     context::Context, error::CompilerError, common_traits::Verify,
/// #     storage_uniquer::TypeValueHash, attribute::Attribute,
/// # };
/// # impl DisplayWithContext for MyAttr {
/// #    fn fmt(&self, _ctx: &Context, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
/// #        todo!()
/// #    }
/// # }
///
/// # impl Verify for MyAttr {
/// #   fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
/// #        todo!()
/// #    }
/// # }
/// ```
///
/// This will generate the following code.
/// ```ignore
///     impl Attribute for MyAttr { ... }
/// ```
/// **Note**: pre-requisite traits for [Attribute] must already be implemented.
///         Additionaly, Hash and PartialEq must be implemented by the type.
#[macro_export]
macro_rules! impl_attr {
    (   $(#[$outer:meta])*
        $structname: ident, $attr_name: literal, $dialect_name: literal) => {
        $(#[$outer])*
        impl $crate::attribute::Attribute for $structname {
            fn eq_attr(&self, other: &dyn Attribute) -> bool {
                other
                    .downcast_ref::<Self>()
                    .map_or(false, |other| other == self)
            }

            fn get_attr_id(&self) -> $crate::attribute::AttrId {
                Self::get_attr_id_static()
            }

            fn get_attr_id_static() -> $crate::attribute::AttrId {
                $crate::attribute::AttrId {
                    name: $crate::attribute::AttrName::new($attr_name),
                    dialect: $crate::dialect::DialectName::new($dialect_name),
                }
            }
        }
        impl $crate::with_context::AttachContext for $structname {}
    }
}
