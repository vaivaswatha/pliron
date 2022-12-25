use crate::{
    common_traits::{Stringable, Verify},
    context::{Context, Ptr},
    dialect::{Dialect, DialectName},
    error::CompilerError,
    r#type::{Type, TypeId, TypeName, TypeObj},
    storage_uniquer::TypeValueHash,
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

#[derive(Hash, PartialEq, Eq)]
pub struct PointerType {
    to: Ptr<TypeObj>,
}

impl PointerType {
    /// Get or create a new pointer type.
    pub fn get(ctx: &mut Context, to: Ptr<TypeObj>) -> Ptr<TypeObj> {
        Type::register_instance(PointerType { to }, ctx)
    }
}

impl Stringable for PointerType {
    fn to_string(&self, ctx: &Context) -> String {
        format!("{}*", self.to.deref(ctx).to_string(ctx))
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

        let int64pointer_ptr = PointerType { to: int64_ptr };
        let int64pointer_ptr = Type::register_instance(int64pointer_ptr, &mut ctx);
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
