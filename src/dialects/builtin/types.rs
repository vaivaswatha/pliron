use crate::{
    common_traits::{Stringable, Verify},
    context::{Context, Ptr},
    error::CompilerError,
    r#type::{Type, TypeObj, TypedHash},
};

#[derive(Hash)]
pub enum Signedness {
    Signed,
    Unsigned,
    Signless,
}

#[derive(Hash)]
pub struct IntegerType {
    width: u64,
    signedness: Signedness,
}

impl IntegerType {
    pub fn create(ctx: &mut Context, width: u64, signedness: Signedness) -> Ptr<TypeObj> {
        Type::register(IntegerType { width, signedness }, ctx)
    }
}

impl Type for IntegerType {
    fn compute_hash(&self) -> TypedHash {
        TypedHash::new(self)
    }
}

impl Stringable for IntegerType {
    fn to_string(&self, _ctx: &Context) -> String {
        match &self.signedness {
            Signedness::Signed => format!("si{}", self.width),
            Signedness::Unsigned => format!("ui{}", self.width),
            Signedness::Signless => format!("i{}", self.width),
        }
    }
}

impl Verify for IntegerType {
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
    fn compute_hash(&self) -> TypedHash {
        TypedHash::new(self)
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
        dialects::builtin::types::{IntegerType, PointerType, Signedness},
    };
    #[test]
    fn test_types() {
        let mut ctx = Context::new();
        let int32_1_ptr = IntegerType::create(&mut ctx, 32, Signedness::Signed);
        let int32_2_ptr = IntegerType::create(&mut ctx, 32, Signedness::Signed);
        let int64_ptr = IntegerType::create(&mut ctx, 64, Signedness::Signed);
        let uint32_ptr = IntegerType::create(&mut ctx, 32, Signedness::Unsigned);

        assert!(int32_1_ptr.deref(&ctx).compute_hash() == int32_2_ptr.deref(&ctx).compute_hash());
        assert!(int32_1_ptr.deref(&ctx).compute_hash() != int64_ptr.deref(&ctx).compute_hash());
        assert!(int32_1_ptr.deref(&ctx).compute_hash() != uint32_ptr.deref(&ctx).compute_hash());
        assert!(int32_1_ptr == int32_2_ptr);
        assert!(int32_1_ptr != int64_ptr);
        assert!(int32_1_ptr != uint32_ptr);

        let int64pointer_ptr = PointerType { to: int64_ptr };
        let int64pointer_ptr = Type::register(int64pointer_ptr, &mut ctx);
        assert!(int64pointer_ptr.deref(&ctx).to_string(&ctx) == "si64*");

        assert!(
            int64_ptr
                .deref(&ctx)
                .downcast_ref::<IntegerType>()
                .unwrap()
                .width
                == 64
        );
    }
}
