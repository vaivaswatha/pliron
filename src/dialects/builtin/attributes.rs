use apint::ApInt;
use sorted_vector_map::SortedVectorMap;

use crate::{
    attribute::{AttrObj, Attribute},
    common_traits::{DisplayWithContext, Verify},
    context::{Context, Ptr},
    dialect::Dialect,
    error::CompilerError,
    impl_attr,
    storage_uniquer::TypeValueHash,
};

/// An attribute containing a string.
/// Similar to MLIR's [StringAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#stringattr).
#[derive(Hash, PartialEq, Eq)]
pub struct StringAttr(String);
impl_attr!(StringAttr, "String", "builtin");

impl StringAttr {
    /// Get or create a new [StringAttr].
    pub fn get(ctx: &mut Context, value: String) -> Ptr<AttrObj> {
        Attribute::register_instance(StringAttr(value), ctx)
    }
}

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
impl_attr!(IntegerAttr, "Integer", "builtin");

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
    /// Get or create a new [IntegerAttr].
    pub fn get(ctx: &mut Context, value: ApInt) -> Ptr<AttrObj> {
        Attribute::register_instance(IntegerAttr(value), ctx)
    }
}

/// An attribute that is a dictionary of other attributes
/// Similar to MLIR's [DictionaryAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#dictionaryattr),
#[derive(Hash, PartialEq, Eq)]
pub struct DictionaryAttr(SortedVectorMap<&'static str, Ptr<AttrObj>>);
impl_attr!(DictionaryAttr, "Dictionary", "builtin");

impl DisplayWithContext for DictionaryAttr {
    fn fmt(&self, _ctx: &Context, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        todo!()
    }
}

impl Verify for DictionaryAttr {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

impl DictionaryAttr {
    /// Get or create a new [DictionaryAttr].
    pub fn get(ctx: &mut Context, value: Vec<(&'static str, Ptr<AttrObj>)>) -> Ptr<AttrObj> {
        let mut dict = SortedVectorMap::with_capacity(value.len());
        for (name, val) in value {
            dict.insert(name, val);
        }
        Attribute::register_instance(DictionaryAttr(dict), ctx)
    }

    /// Lookup a name in the dictionary.
    pub fn lookup(&self, key: &'static str) -> Option<Ptr<AttrObj>> {
        self.0.get(key).copied()
    }
}

pub fn register(dialect: &mut Dialect) {
    StringAttr::register_attr_in_dialect(dialect);
    IntegerAttr::register_attr_in_dialect(dialect);
    DictionaryAttr::register_attr_in_dialect(dialect);
}

#[cfg(test)]
mod tests {
    use apint::ApInt;

    use crate::{
        context::Context,
        dialects::builtin::attributes::{IntegerAttr, StringAttr},
        with_context::AttachContext,
    };

    use super::DictionaryAttr;
    #[test]
    fn test_integer_attributes() {
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
    }

    #[test]
    fn test_string_attributes() {
        let mut ctx = Context::new();

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

    #[test]
    fn test_dictionary_attributes() {
        let mut ctx = Context::new();

        let hello_ptr = StringAttr::get(&mut ctx, "hello".to_string());
        let world_ptr = StringAttr::get(&mut ctx, "world".to_string());

        let dict1 = DictionaryAttr::get(&mut ctx, vec![("hello", hello_ptr), ("world", world_ptr)]);
        let dict2 = DictionaryAttr::get(&mut ctx, vec![("hello", hello_ptr)]);
        let dict1_rev =
            DictionaryAttr::get(&mut ctx, vec![("world", world_ptr), ("hello", hello_ptr)]);
        assert!(dict1 != dict2);
        assert!(dict1 == dict1_rev);

        let dict1_deref = dict1.deref(&ctx);
        let dict1_attr = dict1_deref
            .as_ref()
            .downcast_ref::<DictionaryAttr>()
            .unwrap();
        assert!(dict1_attr.lookup("hello").unwrap() == hello_ptr);
        assert!(dict1_attr.lookup("world").unwrap() == world_ptr);
        assert!(dict1_attr.lookup("hello world").is_none());
    }
}
