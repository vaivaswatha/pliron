use crate::{
    common_traits::{DisplayWithContext, Verify},
    context::{Context, Ptr},
    dialect::{Dialect, DialectName},
    error::CompilerError,
    r#type::{Type, TypeId, TypeName, TypeObj},
    storage_uniquer::TypeValueHash,
    with_context::AttachContext,
};

#[derive(Hash, PartialEq, Eq)]
pub enum Signedness {
    Signed,
    Unsigned,
    Signless,
}

#[derive(Hash, PartialEq, Eq)]
pub struct IntegerType {
    width: u64,
    signedness: Signedness,
}

impl IntegerType {
    /// Get or create a new integer type.
    pub fn get(ctx: &mut Context, width: u64, signedness: Signedness) -> Ptr<TypeObj> {
        Type::register_instance(IntegerType { width, signedness }, ctx)
    }
    /// Get, if it already exists, an integer type.
    pub fn get_existing(ctx: &Context, width: u64, signedness: Signedness) -> Option<Ptr<TypeObj>> {
        Type::get_instance(IntegerType { width, signedness }, ctx)
    }
}

impl Type for IntegerType {
    fn hash_type(&self) -> TypeValueHash {
        TypeValueHash::new(self)
    }

    fn get_type_id(&self) -> TypeId {
        Self::get_type_id_static()
    }

    fn get_type_id_static() -> TypeId {
        TypeId {
            name: TypeName::new("IntegerType"),
            dialect: DialectName::new("builtin"),
        }
    }

    fn eq_type(&self, other: &dyn Type) -> bool {
        other
            .downcast_ref::<Self>()
            .filter(|other| self.eq(other))
            .is_some()
    }
}

impl AttachContext for IntegerType {}

impl DisplayWithContext for IntegerType {
    fn fmt(&self, _ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match &self.signedness {
            Signedness::Signed => write!(f, "si{}", self.width),
            Signedness::Unsigned => write!(f, "ui{}", self.width),
            Signedness::Signless => write!(f, "i{}", self.width),
        }
    }
}

impl Verify for IntegerType {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

#[derive(Hash, PartialEq, Eq)]
pub struct PointerType {
    to: Ptr<TypeObj>,
}

impl PointerType {
    /// Get or create a new pointer type.
    pub fn get(ctx: &mut Context, to: Ptr<TypeObj>) -> Ptr<TypeObj> {
        Type::register_instance(PointerType { to }, ctx)
    }
    /// Get, if it already exists, a pointer type.
    pub fn get_existing(ctx: &Context, to: Ptr<TypeObj>) -> Option<Ptr<TypeObj>> {
        Type::get_instance(PointerType { to }, ctx)
    }
}

impl AttachContext for PointerType {}
impl DisplayWithContext for PointerType {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}*", self.to.with_ctx(ctx))
    }
}

impl Type for PointerType {
    fn hash_type(&self) -> TypeValueHash {
        TypeValueHash::new(self)
    }

    fn get_type_id(&self) -> TypeId {
        Self::get_type_id_static()
    }

    fn get_type_id_static() -> TypeId {
        TypeId {
            name: TypeName::new("PointerType"),
            dialect: DialectName::new("builtin"),
        }
    }

    fn eq_type(&self, other: &dyn Type) -> bool {
        other
            .downcast_ref::<Self>()
            .filter(|other| self.eq(other))
            .is_some()
    }
}

impl Verify for PointerType {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

pub fn register(dialect: &mut Dialect) {
    IntegerType::register_type_in_dialect(dialect);
    PointerType::register_type_in_dialect(dialect);
}

#[cfg(test)]
mod tests {
    use super::Type;
    use crate::{
        context::Context,
        dialects::builtin::types::{IntegerType, PointerType, Signedness},
        with_context::AttachContext,
    };
    #[test]
    fn test_types() {
        let mut ctx = Context::new();
        let int32_1_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int32_2_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signed);
        let uint32_ptr = IntegerType::get(&mut ctx, 32, Signedness::Unsigned);

        assert!(int32_1_ptr.deref(&ctx).hash_type() == int32_2_ptr.deref(&ctx).hash_type());
        assert!(int32_1_ptr.deref(&ctx).hash_type() != int64_ptr.deref(&ctx).hash_type());
        assert!(int32_1_ptr.deref(&ctx).hash_type() != uint32_ptr.deref(&ctx).hash_type());
        assert!(int32_1_ptr == int32_2_ptr);
        assert!(int32_1_ptr != int64_ptr);
        assert!(int32_1_ptr != uint32_ptr);

        assert!(int32_1_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_1_ptr);
        assert!(int32_2_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_1_ptr);
        assert!(int32_2_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_2_ptr);
        assert!(int64_ptr.deref(&ctx).get_self_ptr(&ctx) == int64_ptr);
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) == uint32_ptr);
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) != int32_1_ptr);
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) != int64_ptr);

        let int64pointer_ptr = PointerType { to: int64_ptr };
        let int64pointer_ptr = Type::register_instance(int64pointer_ptr, &mut ctx);
        assert!(int64pointer_ptr.with_ctx(&ctx).to_string() == "si64*");
        assert!(int64pointer_ptr == PointerType::get(&mut ctx, int64_ptr));

        assert!(
            int64_ptr
                .deref(&ctx)
                .downcast_ref::<IntegerType>()
                .unwrap()
                .width
                == 64
        );

        assert!(IntegerType::get_existing(&ctx, 32, Signedness::Signed).unwrap() == int32_1_ptr);
        assert!(PointerType::get_existing(&ctx, int64_ptr).unwrap() == int64pointer_ptr);
    }
}
