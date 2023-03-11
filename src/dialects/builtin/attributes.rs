use apint::ApInt;

use crate::{
    attribute::{AttrId, AttrName, AttrObj, Attribute},
    common_traits::{DisplayWithContext, Verify},
    context::{Context, Ptr},
    dialect::{Dialect, DialectName},
    error::CompilerError,
    storage_uniquer::TypeValueHash,
    with_context::AttachContext,
};

/// An attribute containing a string.
/// Similar to MLIR's [StringAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#stringattr).
#[derive(Hash, PartialEq, Eq)]
pub struct StringAttr(String);

impl Attribute for StringAttr {
    fn hash_attr(&self) -> TypeValueHash {
        TypeValueHash::new(self)
    }

    fn eq_attr(&self, other: &dyn Attribute) -> bool {
        other
            .downcast_ref::<Self>()
            .filter(|other| self.eq(other))
            .is_some()
    }

    fn get_attr_id(&self) -> crate::attribute::AttrId {
        Self::get_attr_id_static()
    }

    fn get_attr_id_static() -> crate::attribute::AttrId
    where
        Self: Sized,
    {
        AttrId {
            name: AttrName::new("String"),
            dialect: DialectName::new("builtin"),
        }
    }
}

impl StringAttr {
    /// Get or create a new integer type.
    pub fn get(ctx: &mut Context, value: String) -> Ptr<AttrObj> {
        Attribute::register_instance(StringAttr(value), ctx)
    }
}

impl AttachContext for StringAttr {}

impl DisplayWithContext for StringAttr {
    fn fmt(&self, _ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Verify for StringAttr {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

/// An attribute containing an integer.
/// Similar to MLIR's [IntegerAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#integerattr).
#[derive(Hash, PartialEq, Eq)]
pub struct IntegerAttr(ApInt);

impl Attribute for IntegerAttr {
    fn hash_attr(&self) -> TypeValueHash {
        TypeValueHash::new(self)
    }

    fn eq_attr(&self, other: &dyn Attribute) -> bool {
        other
            .downcast_ref::<Self>()
            .filter(|other| self.eq(other))
            .is_some()
    }

    fn get_attr_id(&self) -> AttrId {
        Self::get_attr_id_static()
    }

    fn get_attr_id_static() -> AttrId
    where
        Self: Sized,
    {
        AttrId {
            name: AttrName::new("Integer"),
            dialect: DialectName::new("builtin"),
        }
    }
}

impl AttachContext for IntegerAttr {}

impl DisplayWithContext for IntegerAttr {
    fn fmt(&self, _ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "0x{:x}", self.0)
    }
}

impl Verify for IntegerAttr {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

impl IntegerAttr {
    /// Get or create a new integer type.
    pub fn get(ctx: &mut Context, value: ApInt) -> Ptr<AttrObj> {
        Attribute::register_instance(IntegerAttr(value), ctx)
    }
}

pub fn register(dialect: &mut Dialect) {
    StringAttr::register_attr_in_dialect(dialect);
    IntegerAttr::register_attr_in_dialect(dialect);
}

#[cfg(test)]
mod tests {
    use apint::ApInt;

    use crate::{
        context::Context,
        dialects::builtin::attributes::{IntegerAttr, StringAttr},
        with_context::AttachContext,
    };
    #[test]
    fn test_attributes() {
        let mut ctx = Context::new();

        let int64_0_ptr = IntegerAttr::get(&mut ctx, ApInt::from_i64(0));
        let int64_1_ptr = IntegerAttr::get(&mut ctx, ApInt::from_i64(15));
        assert!(int64_0_ptr.deref(&ctx).is::<IntegerAttr>() && int64_0_ptr != int64_1_ptr);
        let int64_0_ptr2 = IntegerAttr::get(&mut ctx, ApInt::from_i64(0));
        assert!(int64_0_ptr == int64_0_ptr2);
        assert!(
            int64_0_ptr.with_ctx(&ctx).to_string() == "0x0"
                && int64_1_ptr.with_ctx(&ctx).to_string() == "0xf"
        );

        let str_0_ptr = StringAttr::get(&mut ctx, "hello".to_string());
        let str_1_ptr = StringAttr::get(&mut ctx, "world".to_string());
        assert!(str_0_ptr.deref(&ctx).is::<StringAttr>() && str_0_ptr != str_1_ptr);
        let str_0_ptr2 = StringAttr::get(&mut ctx, "hello".to_string());
        assert!(str_0_ptr == str_0_ptr2);
        assert!(
            str_0_ptr.with_ctx(&ctx).to_string() == "hello"
                && str_1_ptr.with_ctx(&ctx).to_string() == "world"
        );
    }
}
