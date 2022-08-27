use crate::common_traits::{Stringable, Verify};
use crate::context::{ArenaCell, ArenaObj, Context, Ptr};
use crate::error::CompilerError;

use std::any::TypeId;
use std::collections::hash_map;
use std::hash::{Hash, Hasher};

pub trait Type: Stringable + Verify {
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

    /// Compure and get the hash for this instance of Self.
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
        let hash = t.compute_hash();
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
    use std::{any::TypeId, fmt::Display};

    use super::{Type, TypeHash, TypeObj};
    use crate::{
        common_traits::{Stringable, Verify},
        context::{Context, Ptr},
        error::CompilerError,
    };

    #[derive(Hash)]
    struct IntType {
        pub width: u64,
    }

    impl Type for IntType {
        fn compute_hash(&self) -> TypeHash {
            TypeHash::new(self)
        }
    }

    impl Stringable for IntType {
        fn to_string(&self, _ctx: &Context) -> String {
            format!("i{}", self.width)
        }
    }

    impl Verify for IntType {
        fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
            todo!()
        }
    }

    #[derive(Hash)]
    struct UintType {
        pub width: u64,
    }

    impl Type for UintType {
        fn compute_hash(&self) -> TypeHash {
            TypeHash::new(self)
        }
    }

    impl Stringable for UintType {
        fn to_string(&self, _ctx: &Context) -> String {
            format!("u{}", self.width)
        }
    }

    impl Verify for UintType {
        fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
            todo!()
        }
    }

    #[derive(Hash)]
    struct PointerType {
        pub to: Ptr<TypeObj>,
    }

    impl Stringable for PointerType {
        fn to_string(&self, ctx: &Context) -> String {
            format!("{}*", self.to.deref(ctx).to_string(ctx))
        }
    }

    impl Type for PointerType {
        fn compute_hash(&self) -> TypeHash {
            TypeHash::new(self)
        }
    }

    impl Verify for PointerType {
        fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
            todo!()
        }
    }

    #[test]
    fn test_hashes() {
        let int32_1 = Box::new(IntType { width: 32 });
        let int32_2 = Box::new(IntType { width: 32 });
        let int64 = Box::new(IntType { width: 64 });
        let uint32 = Box::new(UintType { width: 32 });

        assert!(int32_1.compute_hash() == int32_2.compute_hash());
        assert!(int32_1.compute_hash() != int64.compute_hash());
        assert!(int32_1.compute_hash() != uint32.compute_hash());

        let mut ctx = Context::new();
        let int32_1_ptr = IntType::register(int32_1, &mut ctx);
        let int32_2_ptr = IntType::register(int32_2, &mut ctx);
        let int64_ptr = IntType::register(int64, &mut ctx);
        let uint32_ptr = IntType::register(uint32, &mut ctx);
        assert!(int32_1_ptr == int32_2_ptr);
        assert!(int32_1_ptr != int64_ptr);
        assert!(int32_1_ptr != uint32_ptr);

        let int64_ptr = Box::new(PointerType { to: int64_ptr });
        let int64_ptr_ptr = PointerType::register(int64_ptr, &mut ctx);
        assert!(int64_ptr_ptr.deref(&ctx).to_string(&ctx) == "i64*");
    }
}
