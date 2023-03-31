use apint::ApInt;
use sorted_vector_map::SortedVectorMap;

use crate::{
    attribute::{AttrObj, Attribute},
    common_traits::{DisplayWithContext, Verify},
    context::Context,
    dialect::Dialect,
    error::CompilerError,
    impl_attr,
};

/// An attribute containing a string.
/// Similar to MLIR's [StringAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#stringattr).
#[derive(PartialEq, Eq, Clone)]
pub struct StringAttr(String);
impl_attr!(StringAttr, "String", "builtin");

impl StringAttr {
    /// Create a new [StringAttr].
    pub fn create(value: String) -> AttrObj {
        Box::new(StringAttr(value))
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
#[derive(PartialEq, Eq, Clone)]
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
    /// Create a new [IntegerAttr].
    pub fn create(value: ApInt) -> AttrObj {
        Box::new(IntegerAttr(value))
    }
}

/// An attribute that is a small dictionary of other attributes.
/// Implemented as a key-sorted list of key value pairs.
/// Efficient only for small number of keys.
/// Similar to MLIR's [DictionaryAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#dictionaryattr),
#[derive(PartialEq, Eq)]
pub struct SmallDictAttr(SortedVectorMap<&'static str, AttrObj>);
impl_attr!(SmallDictAttr, "SmallDict", "builtin");

impl DisplayWithContext for SmallDictAttr {
    fn fmt(&self, _ctx: &Context, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        todo!()
    }
}

impl Verify for SmallDictAttr {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

impl SmallDictAttr {
    /// Create a new [SmallDictAttr].
    pub fn create(value: Vec<(&'static str, AttrObj)>) -> AttrObj {
        let mut dict = SortedVectorMap::with_capacity(value.len());
        for (name, val) in value {
            dict.insert(name, val);
        }
        Box::new(SmallDictAttr(dict))
    }

    /// Add an entry to the dictionary.
    pub fn insert(&mut self, value: (&'static str, AttrObj)) {
        self.0.insert(value.0, value.1);
    }

    /// Remove an entry from the dictionary.
    pub fn remove(&mut self, key: &'static str) {
        self.0.remove(key);
    }

    /// Lookup a name in the dictionary.
    pub fn lookup<'a>(&'a self, key: &'static str) -> Option<&'a AttrObj> {
        self.0.get(key)
    }
}

pub fn register(dialect: &mut Dialect) {
    StringAttr::register_attr_in_dialect(dialect);
    IntegerAttr::register_attr_in_dialect(dialect);
    SmallDictAttr::register_attr_in_dialect(dialect);
}

#[cfg(test)]
mod tests {
    use apint::ApInt;

    use crate::{
        attribute,
        context::Context,
        dialects::builtin::attributes::{IntegerAttr, StringAttr},
        with_context::AttachContext,
    };

    use super::SmallDictAttr;
    #[test]
    fn test_integer_attributes() {
        let ctx = Context::new();

        let int64_0_ptr = IntegerAttr::create(ApInt::from_i64(0));
        let int64_1_ptr = IntegerAttr::create(ApInt::from_i64(15));
        assert!(int64_0_ptr.is::<IntegerAttr>() && &int64_0_ptr != &int64_1_ptr);
        let int64_0_ptr2 = IntegerAttr::create(ApInt::from_i64(0));
        assert!(int64_0_ptr == int64_0_ptr2);
        assert!(
            int64_0_ptr.with_ctx(&ctx).to_string() == "0x0"
                && int64_1_ptr.with_ctx(&ctx).to_string() == "0xf"
        );
    }

    #[test]
    fn test_string_attributes() {
        let ctx = Context::new();

        let str_0_ptr = StringAttr::create("hello".to_string());
        let str_1_ptr = StringAttr::create("world".to_string());
        assert!(str_0_ptr.is::<StringAttr>() && &str_0_ptr != &str_1_ptr);
        let str_0_ptr2 = StringAttr::create("hello".to_string());
        assert!(str_0_ptr == str_0_ptr2);
        assert!(
            str_0_ptr.with_ctx(&ctx).to_string() == "hello"
                && str_1_ptr.with_ctx(&ctx).to_string() == "world"
        );
    }

    #[test]
    fn test_dictionary_attributes() {
        let hello_attr = StringAttr::create("hello".to_string());
        let world_attr = StringAttr::create("world".to_string());

        let mut dict1 = SmallDictAttr::create(vec![
            ("hello", attribute::clone::<StringAttr>(&hello_attr)),
            ("world", attribute::clone::<StringAttr>(&world_attr)),
        ]);
        let mut dict2 =
            SmallDictAttr::create(vec![("hello", StringAttr::create("hello".to_string()))]);
        let dict1_rev = SmallDictAttr::create(vec![
            ("world", attribute::clone::<StringAttr>(&world_attr)),
            ("hello", attribute::clone::<StringAttr>(&hello_attr)),
        ]);
        assert!(&dict1 != &dict2);
        assert!(dict1 == dict1_rev);

        let dict1_attr = dict1.as_mut().downcast_mut::<SmallDictAttr>().unwrap();
        let dict2_attr = dict2.as_mut().downcast_mut::<SmallDictAttr>().unwrap();
        assert!(dict1_attr.lookup("hello").unwrap() == &hello_attr);
        assert!(dict1_attr.lookup("world").unwrap() == &world_attr);
        assert!(dict1_attr.lookup("hello world").is_none());
        dict2_attr.insert(("world", world_attr));
        assert!(dict1_attr == dict2_attr);

        dict1_attr.remove("hello");
        dict2_attr.remove("hello");
        assert!(&dict1 == &dict2);
    }
}
