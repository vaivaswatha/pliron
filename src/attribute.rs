//! Attributes are known-constant values of operations.
//! See [MLIR Attributes](https://mlir.llvm.org/docs/LangRef/#attributes).
//! Attributes are immutable and are uniqued.

use std::{marker::PhantomData, ops::Deref};

use downcast_rs::{impl_downcast, Downcast};

use crate::{
    common_traits::{DisplayWithContext, Verify},
    context::{ArenaCell, ArenaObj, Context, Ptr},
    dialect::{Dialect, DialectName},
    storage_uniquer::TypeValueHash,
    with_context::AttachContext,
};

/// Basic functionality that every attribute in the IR must implement.
/// Attribute objects (instances of an attribute) are immutable once created,
/// and are uniqued globally. Uniquing is based on the rust-type and contents.
/// So, for example, if we have
/// ```rust,ignore
///     struct Int64Attr {
///         value: u64
///     }
///     impl Attribute for Int64Attr { .. }
/// ```
/// the uniquing will include
///   - [`std::any::TypeId::of::<Int64Attr>()`](std::any::TypeId)
///   - `value`
pub trait Attribute: DisplayWithContext + Verify + Downcast {
    /// Compute and get the hash for this instance of Self.
    fn hash_attr(&self) -> TypeValueHash;
    /// Is self equal to an other Attribute?
    fn eq_attr(&self, other: &dyn Attribute) -> bool;

    /// Get a copyable pointer to this attribute. Unlike in other [ArenaObj]s,
    /// we do not store a self pointer inside the object itself
    /// because that can upset taking automatic hashes of the object.
    fn get_self_ptr(&self, ctx: &Context) -> Ptr<AttrObj> {
        let is = |other: &AttrObj| self.eq_attr(&**other);
        let idx = ctx
            .attr_store
            .get(self.hash_attr(), &is)
            .expect("Unregistered attribute object in existence");
        Ptr {
            idx,
            _dummy: PhantomData::<AttrObj>,
        }
    }

    /// Register an instance of a attribute in the provided [Context]
    /// Returns a pointer to self. If the attribute was already registered,
    /// a pointer to the existing object is returned.
    fn register_instance(t: Self, ctx: &mut Context) -> Ptr<AttrObj>
    where
        Self: Sized,
    {
        let hash = t.hash_attr();
        let idx = ctx
            .attr_store
            .get_or_create_unique(Box::new(t), hash, &eq_attr);
        Ptr {
            idx,
            _dummy: PhantomData::<AttrObj>,
        }
    }

    /// Get an [Attribute]'s static name. This is *not* per instantnce.
    /// It is mostly useful for printing and parsing the attribute.
    /// Uniquing does *not* use this, but instead uses [std::any::TypeId].
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

/// Since we can't store the [Attribute] trait in the arena,
/// we store boxed dyn objects of it instead.
pub type AttrObj = Box<dyn Attribute>;

fn eq_attr(t1: &AttrObj, t2: &AttrObj) -> bool {
    (**t1).eq_attr(&**t2)
}

impl ArenaObj for AttrObj {
    fn get_arena(ctx: &Context) -> &ArenaCell<Self> {
        &ctx.attr_store.unique_store
    }

    fn get_arena_mut(ctx: &mut Context) -> &mut ArenaCell<Self> {
        &mut ctx.attr_store.unique_store
    }

    fn get_self_ptr(&self, ctx: &Context) -> Ptr<Self> {
        self.as_ref().get_self_ptr(ctx)
    }

    fn dealloc_sub_objects(_ptr: Ptr<Self>, _ctx: &mut Context) {
        panic!("Cannot dealloc arena sub-objects of attributes")
    }

    fn remove_references(_ptr: Ptr<Self>, _ctx: &mut Context) {
        panic!("Cannot remove references to attributes")
    }
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
