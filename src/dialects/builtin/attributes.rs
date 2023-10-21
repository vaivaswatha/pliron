use apint::ApInt;
use intertrait::cast_to;
use sorted_vector_map::SortedVectorMap;

use crate::{
    attribute::{AttrObj, Attribute},
    common_traits::Verify,
    context::{Context, Ptr},
    dialect::Dialect,
    error::Result,
    impl_attr, impl_attr_interface,
    printable::{self, Printable},
    r#type::TypeObj,
};

use super::attr_interfaces::TypedAttrInterface;

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

impl From<StringAttr> for String {
    fn from(value: StringAttr) -> Self {
        value.0
    }
}

impl Printable for StringAttr {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Verify for StringAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        todo!()
    }
}

/// An attribute containing an integer.
/// Similar to MLIR's [IntegerAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#integerattr).
#[derive(PartialEq, Eq, Clone)]
pub struct IntegerAttr {
    ty: Ptr<TypeObj>,
    val: ApInt,
}
impl_attr!(IntegerAttr, "Integer", "builtin");

impl Printable for IntegerAttr {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "0x{:x}: {}", self.val, self.ty.disp(ctx))
    }
}

impl Verify for IntegerAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        todo!()
    }
}

impl IntegerAttr {
    /// Create a new [IntegerAttr].
    pub fn create(ty: Ptr<TypeObj>, val: ApInt) -> AttrObj {
        Box::new(IntegerAttr { ty, val })
    }
}

impl From<IntegerAttr> for ApInt {
    fn from(value: IntegerAttr) -> Self {
        value.val
    }
}

impl_attr_interface!(TypedAttrInterface for IntegerAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        self.ty
    }
});

/// A dummy implementation until we have a good one.
#[derive(PartialEq, Clone)]
pub struct APFloat();

/// An attribute containing an floating point value.
/// Similar to MLIR's [FloatAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#floatattr).
/// TODO: Use rustc's APFloat.
#[derive(PartialEq, Clone)]
pub struct FloatAttr(APFloat);
impl_attr!(FloatAttr, "Float", "builtin");

impl Printable for FloatAttr {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "<unimplimented>")
    }
}

impl Verify for FloatAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        todo!()
    }
}

impl FloatAttr {
    /// Create a new [FloatAttr].
    pub fn create(value: APFloat) -> AttrObj {
        Box::new(FloatAttr(value))
    }
}

impl From<FloatAttr> for APFloat {
    fn from(value: FloatAttr) -> Self {
        value.0
    }
}

#[cast_to]
impl TypedAttrInterface for FloatAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        todo!()
    }
}

/// An attribute that is a small dictionary of other attributes.
/// Implemented as a key-sorted list of key value pairs.
/// Efficient only for small number of keys.
/// Similar to MLIR's [DictionaryAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#dictionaryattr),
#[derive(PartialEq, Eq)]
pub struct SmallDictAttr(SortedVectorMap<&'static str, AttrObj>);
impl_attr!(SmallDictAttr, "SmallDict", "builtin");

impl Printable for SmallDictAttr {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        _f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        todo!()
    }
}

impl Verify for SmallDictAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
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
    pub fn insert(&mut self, key: &'static str, val: AttrObj) {
        self.0.insert(key, val);
    }

    /// Remove an entry from the dictionary.
    pub fn remove(&mut self, key: &'static str) {
        self.0.remove(key);
    }

    /// Lookup a name in the dictionary.
    pub fn lookup<'a>(&'a self, key: &'static str) -> Option<&'a AttrObj> {
        self.0.get(key)
    }

    /// Lookup a name in the dictionary, get a mutable reference.
    pub fn lookup_mut<'a>(&'a mut self, key: &'static str) -> Option<&'a mut AttrObj> {
        self.0.get_mut(key)
    }
}

#[derive(PartialEq, Eq)]
pub struct VecAttr(pub Vec<AttrObj>);
impl_attr!(VecAttr, "Vec", "builtin");

impl VecAttr {
    pub fn create(value: Vec<AttrObj>) -> AttrObj {
        Box::new(VecAttr(value))
    }
}

impl Printable for VecAttr {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        _f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        todo!()
    }
}

impl Verify for VecAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        todo!()
    }
}

/// Represent attributes that only have meaning from their existence.
/// See [UnitAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#unitattr) in MLIR.
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct UnitAttr();
impl_attr!(UnitAttr, "Unit", "builtin");

impl UnitAttr {
    pub fn create() -> AttrObj {
        Box::new(UnitAttr())
    }
}

impl Printable for UnitAttr {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{}", self.get_attr_id().disp(ctx))
    }
}

impl Verify for UnitAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

/// An attribute that does nothing but hold a Type.
/// Same as MLIR's [TypeAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#typeattr).
#[derive(PartialEq, Eq, Clone)]
pub struct TypeAttr(Ptr<TypeObj>);
impl_attr!(TypeAttr, "Type", "builtin");

impl TypeAttr {
    pub fn create(ty: Ptr<TypeObj>) -> AttrObj {
        Box::new(TypeAttr(ty))
    }
}

impl Printable for TypeAttr {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{}<{}>", self.get_attr_id().disp(ctx), self.0.disp(ctx))
    }
}

impl Verify for TypeAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

#[cast_to]
impl TypedAttrInterface for TypeAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        self.0
    }
}

pub fn register(dialect: &mut Dialect) {
    StringAttr::register_attr_in_dialect(dialect);
    IntegerAttr::register_attr_in_dialect(dialect);
    SmallDictAttr::register_attr_in_dialect(dialect);
    VecAttr::register_attr_in_dialect(dialect);
    UnitAttr::register_attr_in_dialect(dialect);
    TypeAttr::register_attr_in_dialect(dialect);
}

#[cfg(test)]
mod tests {
    use apint::ApInt;

    use crate::{
        attribute::{self, attr_cast},
        context::Context,
        dialects::builtin::{
            attr_interfaces::TypedAttrInterface,
            attributes::{IntegerAttr, StringAttr},
            types::{IntegerType, Signedness},
        },
        printable::Printable,
    };

    use super::{SmallDictAttr, TypeAttr, VecAttr};
    #[test]
    fn test_integer_attributes() {
        let mut ctx = Context::new();
        let i64_ty = IntegerType::get(&mut ctx, 64, Signedness::Signed);

        let int64_0_ptr = IntegerAttr::create(i64_ty, ApInt::from_i64(0));
        let int64_1_ptr = IntegerAttr::create(i64_ty, ApInt::from_i64(15));
        assert!(int64_0_ptr.is::<IntegerAttr>() && &int64_0_ptr != &int64_1_ptr);
        let int64_0_ptr2 = IntegerAttr::create(i64_ty, ApInt::from_i64(0));
        assert!(int64_0_ptr == int64_0_ptr2);
        assert_eq!(
            int64_0_ptr.disp(&ctx).to_string(),
            "0x0: builtin.integer <si64>"
        );
        assert_eq!(
            int64_1_ptr.disp(&ctx).to_string(),
            "0xf: builtin.integer <si64>"
        );
        assert!(
            ApInt::from(int64_0_ptr.downcast_ref::<IntegerAttr>().unwrap().clone()).is_zero()
                && ApInt::resize_to_i64(&ApInt::from(
                    int64_1_ptr.downcast_ref::<IntegerAttr>().unwrap().clone()
                )) == 15
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
            str_0_ptr.disp(&ctx).to_string() == "hello"
                && str_1_ptr.disp(&ctx).to_string() == "world"
        );
        assert!(
            String::from(str_0_ptr.downcast_ref::<StringAttr>().unwrap().clone()) == "hello"
                && String::from(str_1_ptr.downcast_ref::<StringAttr>().unwrap().clone()) == "world",
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
        dict2_attr.insert("world", world_attr);
        assert!(dict1_attr == dict2_attr);

        dict1_attr.remove("hello");
        dict2_attr.remove("hello");
        assert!(&dict1 == &dict2);
    }

    #[test]
    fn test_vec_attributes() {
        let hello_attr = StringAttr::create("hello".to_string());
        let world_attr = StringAttr::create("world".to_string());

        let vec_attr = VecAttr::create(vec![
            attribute::clone::<StringAttr>(&hello_attr),
            attribute::clone::<StringAttr>(&world_attr),
        ]);
        let vec = vec_attr.downcast_ref::<VecAttr>().unwrap();
        assert!(vec.0.len() == 2 && vec.0[0] == hello_attr && vec.0[1] == world_attr);
    }

    #[test]
    fn test_type_attributes() {
        let mut ctx = Context::new();

        let ty = IntegerType::get(&mut ctx, 64, Signedness::Signed);
        let ty_attr = TypeAttr::create(ty);

        let ty_interface = attr_cast::<dyn TypedAttrInterface>(&*ty_attr).unwrap();
        assert!(ty_interface.get_type() == ty);
    }
}
