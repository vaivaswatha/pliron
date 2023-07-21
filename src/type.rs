//! Every SSA value, such as operation results or block arguments
//! has a type defined by the type system.
//!
//! The type system is open, with no fixed list of types,
//! and there are no restrictions on the abstractions they represent.
//!
//! See [MLIR Types](https://mlir.llvm.org/docs/DefiningDialects/AttributesAndTypes/#types)
//!
//! The [impl_type](crate::impl_type) macro can be used to implement [Type] for a rust type.

use crate::common_traits::Verify;
use crate::context::{private::ArenaObj, ArenaCell, Context, Ptr};
use crate::dialect::{Dialect, DialectName};
use crate::printable::{self, Printable};
use crate::storage_uniquer::TypeValueHash;

use downcast_rs::{impl_downcast, Downcast};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::Deref;

/// Basic functionality that every type in the IR must implement.
/// Type objects (instances of a Type) are (mostly) immutable once created,
/// and are uniqued globally. Uniquing is based on the type name (i.e.,
/// the rust type being defined) and its contents.
///
/// So, for example, if we have
/// ```rust,ignore
///     struct IntType {
///         width: u64
///     }
///     impl Type for IntType { .. }
/// ```
/// the uniquing will include
///   - [`std::any::TypeId::of::<IntType>()`](std::any::TypeId)
///   - `width`
///
/// Types *can* have mutable contents that can be modified *after*
/// the type is created. This enables creation of recursive types.
/// In such a case, it is up to the type definition to ensure that
///   1. It manually implements Hash, ignoring these mutable fields.
///   2. A proper distinguisher content (such as a string), that is part
///      of the hash, is used so that uniquing still works.
pub trait Type: Printable + Verify + Downcast + Sync {
    /// Compute and get the hash for this instance of Self.
    /// Hash collisions can be a possibility.
    fn hash_type(&self) -> TypeValueHash;
    /// Is self equal to an other Type?
    fn eq_type(&self, other: &dyn Type) -> bool;

    /// Get a copyable pointer to this type.
    // Unlike in other [ArenaObj]s,
    // we do not store a self pointer inside the object itself
    // because that can upset taking automatic hashes of the object.
    fn get_self_ptr(&self, ctx: &Context) -> Ptr<TypeObj> {
        let is = |other: &TypeObj| self.eq_type(&**other);
        let idx = ctx
            .type_store
            .get(self.hash_type(), &is)
            .expect("Unregistered type object in existence");
        Ptr {
            idx,
            _dummy: PhantomData::<TypeObj>,
        }
    }

    /// Register an instance of a type in the provided [Context]
    /// Returns a pointer to self. If the type was already registered,
    /// a pointer to the existing object is returned.
    fn register_instance(t: Self, ctx: &mut Context) -> Ptr<TypeObj>
    where
        Self: Sized,
    {
        let hash = t.hash_type();
        let idx = ctx
            .type_store
            .get_or_create_unique(Box::new(t), hash, &TypeObj::eq);
        Ptr {
            idx,
            _dummy: PhantomData::<TypeObj>,
        }
    }

    /// If an instance of `t` already exists, get a [Ptr] to it.
    /// Consumes `t` either way.
    fn get_instance(t: Self, ctx: &Context) -> Option<Ptr<TypeObj>>
    where
        Self: Sized,
    {
        let is = |other: &TypeObj| t.eq_type(&**other);
        ctx.type_store.get(t.hash_type(), &is).map(|idx| Ptr {
            idx,
            _dummy: PhantomData::<TypeObj>,
        })
    }

    /// Get a Type's static name. This is *not* per instantiation of the type.
    /// It is mostly useful for printing and parsing the type.
    /// Uniquing does *not* use this, but instead uses [std::any::TypeId].
    fn get_type_id(&self) -> TypeId;

    /// Same as [get_type_id](Self::get_type_id), but without the self reference.
    fn get_type_id_static() -> TypeId
    where
        Self: Sized;

    /// Register this Type's [TypeId] in the dialect it belongs to.
    /// **Warning**: No check is made as to whether this type is already registered
    ///  in `dialect`.
    fn register_type_in_dialect(dialect: &mut Dialect)
    where
        Self: Sized,
    {
        dialect.add_type(Self::get_type_id_static());
    }
}
impl_downcast!(Type);

#[derive(Clone, Hash, PartialEq, Eq)]
/// A Type's name (not including it's dialect).
pub struct TypeName(String);

impl TypeName {
    /// Create a new TypeName.
    pub fn new(name: &str) -> TypeName {
        TypeName(name.to_string())
    }
}

impl Deref for TypeName {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Printable for TypeName {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A combination of a Type's name and its dialect.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct TypeId {
    pub dialect: DialectName,
    pub name: TypeName,
}

impl Printable for TypeId {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{}.{}", self.dialect.disp(ctx), self.name.disp(ctx))
    }
}

/// Since we can't store the [Type] trait in the arena,
/// we store boxed dyn objects of it instead.
pub type TypeObj = Box<dyn Type>;

impl PartialEq for TypeObj {
    fn eq(&self, other: &Self) -> bool {
        (**self).eq_type(&**other)
    }
}

impl Eq for TypeObj {}

impl Hash for TypeObj {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write(&u64::from(self.hash_type()).to_ne_bytes())
    }
}

impl ArenaObj for TypeObj {
    fn get_arena(ctx: &Context) -> &ArenaCell<Self> {
        &ctx.type_store.unique_store
    }

    fn get_arena_mut(ctx: &mut Context) -> &mut ArenaCell<Self> {
        &mut ctx.type_store.unique_store
    }

    fn get_self_ptr(&self, ctx: &Context) -> Ptr<Self> {
        self.as_ref().get_self_ptr(ctx)
    }

    fn dealloc_sub_objects(_ptr: Ptr<Self>, _ctx: &mut Context) {
        panic!("Cannot dealloc arena sub-objects of types")
    }
}

impl Printable for TypeObj {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        self.as_ref().fmt(ctx, state, f)
    }
}

impl Verify for TypeObj {
    fn verify(&self, ctx: &Context) -> Result<(), crate::error::CompilerError> {
        self.as_ref().verify(ctx)
    }
}

/// impl [Type] for a rust type
///
/// Usage:
/// ```
/// #[derive(PartialEq, Eq, Hash)]
/// struct MyType { }
/// impl_type!(
///     /// MyType is mine
///     MyType,
///     "name",
///     "dialect"
/// );
/// # use pliron::{
/// #     impl_type, printable::{self, Printable},
/// #     context::Context, error::CompilerError, common_traits::Verify,
/// #     storage_uniquer::TypeValueHash, r#type::Type,
/// # };
/// # impl Printable for MyType {
/// #    fn fmt(&self,
/// #           _ctx: &Context,
/// #          _state: &printable::State,
/// #          _f: &mut core::fmt::Formatter<'_>)
/// #    -> core::fmt::Result
/// #    {
/// #        todo!()
/// #    }
/// # }
/// #
/// # impl Verify for MyType {
/// #   fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
/// #        todo!()
/// #    }
/// # }
/// ```
/// **Note**: pre-requisite traits for [Type] must already be implemented.
///         Additionaly, Hash and Eq must be implemented by the rust type.
#[macro_export]
macro_rules! impl_type {
    (   $(#[$outer:meta])*
        $structname: ident, $type_name: literal, $dialect_name: literal) => {
        $(#[$outer])*
        impl $crate::r#type::Type for $structname {
            fn hash_type(&self) -> TypeValueHash {
                TypeValueHash::new(self)
            }

            fn eq_type(&self, other: &dyn Type) -> bool {
                other
                    .downcast_ref::<Self>()
                    .map_or(false, |other| other == self)
            }

            fn get_type_id(&self) -> $crate::r#type::TypeId {
                Self::get_type_id_static()
            }

            fn get_type_id_static() -> $crate::r#type::TypeId {
                $crate::r#type::TypeId {
                    name: $crate::r#type::TypeName::new($type_name),
                    dialect: $crate::dialect::DialectName::new($dialect_name),
                }
            }
        }
    }
}
