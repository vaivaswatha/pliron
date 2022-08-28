use crate::common_traits::{Stringable, Verify};
use crate::context::{ArenaCell, ArenaObj, Context, Ptr};
use crate::error::CompilerError;

use downcast_rs::{impl_downcast, Downcast};
use std::any::TypeId;
use std::collections::hash_map;
use std::hash::{Hash, Hasher};

pub trait Type: Stringable + Verify + Downcast {
    /// Basic functionality that every type in the IR must implement.
    /// Types are (mostly) immutable once created, and are uniqued globally.
    /// Uniquing is based on the type name and contents.
    /// So, for example, if we have
    /// ```rust,ignore
    ///     struct IntType {
    ///         width: u64
    ///     }
    ///     impl Type for IntType { }
    /// ```
    /// the uniquing will include "IntType" as well as the `width` itself.
    ///
    /// Types *can* have mutable contents that can be modified *after*
    /// the type is created. This enables creation of recursive types.
    /// In such a case, it is up to the type definition to ensure that
    ///   1. It manually implements Hash, ignoring these mutable fields.
    ///   2. A proper distinguisher content (such as a string), that is part
    ///      of the hash, is used so that uniquing still works.

    /// Compute and get the hash for this instance of Self.
    fn compute_hash(&self) -> TypeHash;

    /// Get a copyable pointer to this type. Unlike in other ArenaObjs,
    /// we do not store a self pointer inside the object itself
    /// because that can upset taking automatic hashes of the object.
    fn get_self_ptr(&self, ctx: &Context) -> Ptr<TypeObj> {
        let hash = self.compute_hash();
        *ctx.typehash_typeptr_map
            .get(&hash)
            .expect(format!("Type {} not registered", self.to_string(ctx)).as_str())
    }

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

#[derive(Hash, Eq, PartialEq)]
pub struct TypeHash {
    hash: u64,
}

impl TypeHash {
    pub fn new<T: Type + Hash + 'static>(t: &T) -> TypeHash {
        use hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();
        t.hash(&mut hasher);
        TypeId::of::<T>().hash(&mut hasher);
        TypeHash {
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
