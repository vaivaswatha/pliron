use crate::{
    common_traits::{Stringable, Verify},
    context::{Context, Ptr},
    error::CompilerError,
    r#type::{Type, TypeHash, TypeObj},
};

#[derive(Hash)]
pub struct IntType {
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
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

#[derive(Hash)]
pub struct UintType {
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
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

#[derive(Hash)]
pub struct PointerType {
    to: Ptr<TypeObj>,
}

impl PointerType {
    pub fn create(ctx: &mut Context, to: Ptr<TypeObj>) -> Ptr<TypeObj> {
        Type::register(PointerType { to }, ctx)
    }
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
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::Type;
    use crate::{
        context::Context,
        dialects::builtin::types::{IntType, PointerType, UintType},
    };
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
    }
}
