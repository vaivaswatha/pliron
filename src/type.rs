use crate::context::{ArenaCell, ArenaObj, Context, Ptr};
use crate::error::CompilerError;

use std::any::TypeId;
use std::collections::hash_map;
use std::fmt::Display;
use std::hash::{Hash, Hasher};

pub trait Type: Display {
    /// Basic functionality that every type in the IR must implement.
    /// Types are immutable once created, and are uniqued globally.
    /// Uniquing is based on the type name and contents.
    /// So, for example, if we have
    /// ```
    ///     struct IntType {
    ///         width: u64
    ///     }
    ///     impl Type for IntType { }
    /// ```
    /// the uniquing will include "IntType" as well as the `width` itself.

    /// Verification, called before registering the type in context.
    fn verify(&self) -> Result<(), CompilerError>;
    /// Get hash for this instance of Self.
    fn get_hash(&self) -> TypeHash;

    /// Get a copyable pointer to this type. Unlike in other ArenaObjs,
    /// we do not store a self pointer inside the object itself
    /// because that can upset taking automatic hashes of the object.
    fn get_self_ptr(&self, ctx: &Context) -> Ptr<TypeObj> {
        let hash = self.get_hash();
        *ctx.typehash_typeptr_map
            .get(&hash)
            .expect(format!("Type {} not registered", &self).as_str())
    }

    /// Downcast a dynamic Type object to it's concrete implementation.
    fn downcast<T: Type>(&self) -> Option<&T>
    where
        Self: Sized,
    {
        todo!()
    }

    fn register(t: TypeObj, ctx: &mut Context) -> Ptr<TypeObj>
    where
        Self: Sized,
    {
        let hash = t.get_hash();
        // entry.or_insert_with(|| ArenaObj::alloc(ctx, |p: Ptr<TypeObj>| t))
        match ctx.typehash_typeptr_map.get(&hash) {
            Some(val) => *val,
            None => {
                let val = ArenaObj::alloc(ctx, |_: Ptr<TypeObj>| t);
                ctx.typehash_typeptr_map.insert(hash, val);
                val
            }
        }
    }
}

#[derive(Hash, Eq, PartialEq)]
pub struct TypeHash {
    hash: u64,
}

impl TypeHash {
    fn new<T: Type + Hash + 'static>(t: &T) -> TypeHash {
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
        panic!("Types, once created shouldn't be modified")
    }

    fn remove_references(_ptr: Ptr<Self>, _ctx: &mut Context) {
        panic!("Types, once created shouldn't be removed")
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Display;

    use super::{Type, TypeHash};
    use crate::{context::Context, error::CompilerError};

    #[derive(Hash)]
    struct Int {
        pub width: u64,
    }

    impl Type for Int {
        fn verify(&self) -> Result<(), CompilerError> {
            todo!()
        }

        fn get_hash(&self) -> TypeHash {
            TypeHash::new(self)
        }
    }

    impl Display for Int {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "i{}", self.width)
        }
    }

    #[derive(Hash)]
    struct Uint {
        pub width: u64,
    }

    impl Type for Uint {
        fn verify(&self) -> Result<(), CompilerError> {
            todo!()
        }

        fn get_hash(&self) -> TypeHash {
            TypeHash::new(self)
        }
    }

    impl Display for Uint {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "u{}", self.width)
        }
    }

    #[test]
    fn test_hashes() {
        let int32_1 = Box::new(Int { width: 32 });
        let int32_2 = Box::new(Int { width: 32 });
        let int64 = Box::new(Int { width: 64 });
        let uint32 = Box::new(Uint { width: 32 });

        assert!(int32_1.get_hash() == int32_2.get_hash());
        assert!(int32_1.get_hash() != int64.get_hash());
        assert!(int32_1.get_hash() != uint32.get_hash());

        let mut ctx = Context::new();
        let int32_1_ptr = Int::register(int32_1, &mut ctx);
        let int32_2_ptr = Int::register(int32_2, &mut ctx);
        let int64_ptr = Int::register(int64, &mut ctx);
        let uint32_ptr = Int::register(uint32, &mut ctx);
        assert!(int32_1_ptr == int32_2_ptr);
        assert!(int32_1_ptr != int64_ptr);
        assert!(int32_1_ptr != uint32_ptr);
    }
}
