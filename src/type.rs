//! Every SSA value, such as operation results or block arguments
//! has a type defined by the type system.
//!
//! The type system is open, with no fixed list of types,
//! and there are no restrictions on the abstractions they represent.
//!
//! See [MLIR Types](https://mlir.llvm.org/docs/DefiningDialects/AttributesAndTypes/#types)
//!
//! The [def_type](pliron_derive::def_type) proc macro from [pliron-derive]
//! can be used to implement [Type] for a rust type.

use crate::common_traits::Verify;
use crate::context::{private::ArenaObj, ArenaCell, Context, Ptr};
use crate::dialect::{Dialect, DialectName};
use crate::error::Result;
use crate::identifier::Identifier;
use crate::input_err;
use crate::irfmt::parsers::spaced;
use crate::location::Located;
use crate::parsable::{Parsable, ParseResult, ParserFn, StateStream};
use crate::printable::{self, Printable};
use crate::storage_uniquer::TypeValueHash;

use combine::{parser, Parser};
use downcast_rs::{impl_downcast, Downcast};
use std::fmt::Debug;
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
pub trait Type: Printable + Verify + Downcast + Sync + Debug {
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
    fn register_type_in_dialect(dialect: &mut Dialect, parser: ParserFn<(), Ptr<TypeObj>>)
    where
        Self: Sized,
    {
        dialect.add_type(Self::get_type_id_static(), parser);
    }
}
impl_downcast!(Type);

/// Trait for IR entities that have a direct type.
pub trait Typed {
    /// Get the [Type] of the current entity.
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj>;
}

impl Typed for Ptr<TypeObj> {
    fn get_type(&self, _ctx: &Context) -> Ptr<TypeObj> {
        *self
    }
}

impl Typed for dyn Type {
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.get_self_ptr(ctx)
    }
}

impl<T: Typed + ?Sized> Typed for &T {
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        (*self).get_type(ctx)
    }
}

impl<T: Typed + ?Sized> Typed for &mut T {
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        (**self).get_type(ctx)
    }
}

impl<T: Typed + ?Sized> Typed for Box<T> {
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        (**self).get_type(ctx)
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
/// A Type's name (not including it's dialect).
pub struct TypeName(Identifier);

impl TypeName {
    /// Create a new TypeName.
    pub fn new(name: &str) -> TypeName {
        TypeName(name.into())
    }
}

impl Deref for TypeName {
    type Target = Identifier;

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

impl Parsable for TypeName {
    type Arg = ();
    type Parsed = TypeName;

    fn parse<'a>(
        state_stream: &mut crate::parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        Identifier::parser(())
            .map(|name| TypeName::new(&name))
            .parse_stream(state_stream)
            .into()
    }
}

/// A combination of a Type's name and its dialect.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct TypeId {
    pub dialect: DialectName,
    pub name: TypeName,
}

impl Parsable for TypeId {
    type Arg = ();
    type Parsed = TypeId;

    // Parses (but does not validate) a TypeId.
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        let mut parser = DialectName::parser(())
            .skip(parser::char::char('.'))
            .and(TypeName::parser(()))
            .map(|(dialect, name)| TypeId { dialect, name });
        parser.parse_stream(state_stream).into()
    }
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
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.get_type_id().fmt(ctx, state, f)?;
        Printable::fmt(self.deref(), ctx, state, f)
    }
}

impl Parsable for Ptr<TypeObj> {
    type Arg = ();
    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        let loc = state_stream.loc();
        let type_id_parser = spaced(TypeId::parser(()));

        let mut type_parser = type_id_parser.then(move |type_id: TypeId| {
            // This clone is to satify the borrow checker.
            let loc = loc.clone();
            combine::parser(move |parsable_state: &mut StateStream<'a>| {
                let state = &parsable_state.state;
                let dialect = state
                    .ctx
                    .dialects
                    .get(&type_id.dialect)
                    .expect("Dialect name parsed but dialect isn't registered");
                let Some(type_parser) = dialect.types.get(&type_id) else {
                    input_err!(loc.clone(), "Unregistered type {}", type_id.disp(state.ctx))?
                };
                type_parser(&(), ()).parse_stream(parsable_state).into()
            })
        });

        type_parser.parse_stream(state_stream).into_result()
    }
}

impl Verify for TypeObj {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.as_ref().verify(ctx)
    }
}
