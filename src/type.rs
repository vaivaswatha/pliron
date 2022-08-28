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

#[cfg(test)]
mod tests {
    use super::{Type, TypeHash, TypeObj};
    use crate::{
        common_traits::{Stringable, Verify},
        context::{Context, Ptr},
        error::CompilerError,
    };
    use std::{collections::HashSet, fmt::Pointer, hash::Hash};

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

    /// Represents a c-like struct type.
    /// Limitations and warnings on its usage are similar to that in MLIR.
    /// https://mlir.llvm.org/docs/Dialects/LLVM/#structure-types
    struct StructType {
        name: String,
        fields: Vec<(String, Ptr<TypeObj>)>,
    }

    impl Verify for StructType {
        fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
            todo!()
        }
    }

    impl Stringable for StructType {
        fn to_string(&self, ctx: &Context) -> String {
            use std::cell::RefCell;
            // Ugly, but also the simplest way to avoid infinite recursion.
            // MLIR does the same: see LLVMTypeSyntax::printStructType.
            thread_local! {
                static IN_PRINTING: RefCell<HashSet<String>>  = RefCell::new(HashSet::new());
            }
            let in_printing = IN_PRINTING.with(|f| f.borrow().contains(&self.name));
            if in_printing {
                return self.name.clone();
            }
            IN_PRINTING.with(|f| f.borrow_mut().insert(self.name.clone()));
            let mut s = format!("{} {{ ", self.name);
            for field in &self.fields {
                s += [
                    field.0.clone(),
                    ": ".to_string(),
                    field.1.deref(ctx).to_string(ctx),
                    ", ".to_string(),
                ]
                .concat()
                .as_str();
            }
            s += "}";
            // Done processing this struct. Remove it from the stack.
            IN_PRINTING.with(|f| f.borrow_mut().remove(&self.name));
            s
        }
    }

    impl Hash for StructType {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.name.hash(state);
            // NOTE: Does not hash the fields due to possibility
            // of recursive types.
        }
    }

    impl Type for StructType {
        fn compute_hash(&self) -> TypeHash {
            TypeHash::new(self)
        }
    }

    #[test]
    fn test_types() {
        let int32_1 = IntType { width: 32 };
        let int32_2 = IntType { width: 32 };
        let int64 = IntType { width: 64 };
        let uint32 = UintType { width: 32 };

        assert!(int32_1.compute_hash() == int32_2.compute_hash());
        assert!(int32_1.compute_hash() != int64.compute_hash());
        assert!(int32_1.compute_hash() != uint32.compute_hash());

        let mut ctx = Context::new();
        let int32_1_ptr = Type::register(int32_1, &mut ctx);
        let int32_2_ptr = Type::register(int32_2, &mut ctx);
        let int64_ptr = Type::register(int64, &mut ctx);
        let uint32_ptr = Type::register(uint32, &mut ctx);
        assert!(int32_1_ptr == int32_2_ptr);
        assert!(int32_1_ptr != int64_ptr);
        assert!(int32_1_ptr != uint32_ptr);

        let int64pointer_ptr = PointerType { to: int64_ptr };
        let int64pointer_ptr = Type::register(int64pointer_ptr, &mut ctx);
        assert!(int64pointer_ptr.deref(&ctx).to_string(&ctx) == "i64*");

        assert!(
            int64_ptr
                .deref(&ctx)
                .downcast_ref::<IntType>()
                .unwrap()
                .width
                == 64
        );

        // Let's build a linked list structure and verify it.
        let list_struct = Type::register(
            StructType {
                name: "LinkedList".to_string(),
                fields: vec![],
            },
            &mut ctx,
        );
        let list_ptr = Type::register(PointerType { to: list_struct }, &mut ctx);
        {
            // Modify the fields. These aren't part of what's originally built.
            let mut typeref = list_struct.deref_mut(&ctx);
            let list_ref = typeref.downcast_mut::<StructType>().unwrap();
            list_ref.fields = vec![
                ("data".to_string(), int64_ptr),
                ("next".to_string(), list_ptr),
            ];
        }
        assert!(
            list_struct
                .deref(&ctx)
                .downcast_ref::<StructType>()
                .unwrap()
                .to_string(&ctx)
                == "LinkedList { data: i64, next: LinkedList*, }"
        );
    }
}
