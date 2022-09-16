use crate::common_traits::{Stringable, Verify};
use crate::context::{ArenaCell, ArenaObj, Context, Ptr};
use crate::dialect::{Dialect, DialectName};

use downcast_rs::{impl_downcast, Downcast};
use rustc_hash::FxHasher;
use std::hash::{Hash, Hasher};
use std::ops::Deref;

/// Basic functionality that every type in the IR must implement.
/// Type objects (instances of a Type) are (mostly) immutable once created,
/// and are uniqued globally. Uniquing is based on the type name and contents.
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
pub trait Type: Stringable + Verify + Downcast {
    /// Compute and get the hash for this instance of Self.
    fn compute_hash(&self) -> TypedHash;

    /// Get a copyable pointer to this type. Unlike in other [ArenaObj]s,
    /// we do not store a self pointer inside the object itself
    /// because that can upset taking automatic hashes of the object.
    fn get_self_ptr(&self, ctx: &Context) -> Ptr<TypeObj> {
        let hash = self.compute_hash();
        *ctx.typehash_typeptr_map
            .get(&hash)
            .unwrap_or_else(|| panic!("Type {} not registered", self.to_string(ctx)))
    }

    /// Register an instance of a type in the provided [Context]
    /// Returns a pointer to self. If the type was already registered,
    /// a pointer to the existing object is returned.
    fn register_instance(t: Self, ctx: &mut Context) -> Ptr<TypeObj>
    where
        Self: Sized,
    {
        let hash = t.compute_hash();
        // entry.or_insert_with(|| ArenaObj::alloc(ctx, |p: Ptr<TypeObj>| t))
        match ctx.typehash_typeptr_map.get(&hash) {
            Some(val) => *val,
            None => {
                let val = ArenaObj::alloc(ctx, |_: Ptr<TypeObj>| Box::new(t));
                ctx.typehash_typeptr_map.insert(hash, val);
                val
            }
        }
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

/// A combination of a Type's name and its dialect.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct TypeId {
    pub dialect: DialectName,
    pub name: TypeName,
}

/// Computes the hash of a value and its type.
/// ```rust
///     use pliron::r#type::TypedHash;
///     #[derive(Hash)]
///     struct A { i: u64 }
///     #[derive(Hash)]
///     struct B { i: u64 }
///     let x = A { i: 10 };
///     let y = B { i: 10 };
///     assert!(TypedHash::new(&x) != TypedHash::new(&y));
/// ```
#[derive(Hash, Eq, PartialEq)]
pub struct TypedHash {
    hash: u64,
}

impl TypedHash {
    /// Hash a value and its type together.
    pub fn new<T: Hash + 'static>(t: &T) -> TypedHash {
        let mut hasher = FxHasher::default();
        t.hash(&mut hasher);
        std::any::TypeId::of::<T>().hash(&mut hasher);
        TypedHash {
            hash: hasher.finish(),
        }
    }
}

/// Since we can't store the Type trait in the arena,
/// we store boxed dyn objects of Type instead.
pub type TypeObj = Box<dyn Type>;

impl ArenaObj for TypeObj {
    fn get_arena(ctx: &Context) -> &ArenaCell<Self> {
        &ctx.types
    }

    fn get_arena_mut(ctx: &mut Context) -> &mut ArenaCell<Self> {
        &mut ctx.types
    }

    fn get_self_ptr(&self, ctx: &Context) -> Ptr<Self> {
        self.as_ref().get_self_ptr(ctx)
    }

    fn dealloc_sub_objects(_ptr: Ptr<Self>, _ctx: &mut Context) {
        panic!("Cannot dealloc arena sub-objects of types")
    }

    fn remove_references(_ptr: Ptr<Self>, _ctx: &mut Context) {
        panic!("Cannot remove references to types")
    }
}
