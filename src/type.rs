use crate::common_traits::{Stringable, Verify};
use crate::context::{ArenaCell, ArenaObj, Context, Ptr};

use downcast_rs::{impl_downcast, Downcast};
use std::any::TypeId;
use std::collections::hash_map;
use std::hash::{Hash, Hasher};

/// Basic functionality that every type in the IR must implement.
/// Types are (mostly) immutable once created, and are uniqued globally.
/// Uniquing is based on the type name and contents.
/// So, for example, if we have
/// ```rust
///     use pliron::r#type::{Type, TypedHash};
///     #[derive(Hash)]
///     struct IntType {
///         width: u64
///     }
///     # use pliron::{common_traits::{Stringable, Verify}, context::Context, error::CompilerError};
///     # impl Stringable for IntType { fn to_string(&self, _ctx: &Context) -> String { todo!() } }
///     # impl Verify for IntType { fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> { todo!() } }
///     impl Type for IntType {
///         fn compute_hash(&self) -> TypedHash { TypedHash::new(self) }
///     }
/// ```
/// the uniquing will include "IntType" as well as the `width` itself.
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

    /// Get a copyable pointer to this type. Unlike in other ArenaObjs,
    /// we do not store a self pointer inside the object itself
    /// because that can upset taking automatic hashes of the object.
    fn get_self_ptr(&self, ctx: &Context) -> Ptr<TypeObj> {
        let hash = self.compute_hash();
        *ctx.typehash_typeptr_map
            .get(&hash)
            .unwrap_or_else(|| panic!("Type {} not registered", self.to_string(ctx)))
    }

    /// Register a type in the provided Context and return a pointer to self.
    /// If the type was already registered, a pointer to the existing object is returned.
    fn register(t: Self, ctx: &mut Context) -> Ptr<TypeObj>
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
}
impl_downcast!(Type);

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
        use hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();
        t.hash(&mut hasher);
        TypeId::of::<T>().hash(&mut hasher);
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
