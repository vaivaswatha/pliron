use apint::ApInt;
use combine::{any, between, easy, many, none_of, token, ParseResult, Parser, Positioned};
use sorted_vector_map::SortedVectorMap;
use thiserror::Error;

use crate::{
    attribute::{AttrObj, Attribute},
    common_traits::Verify,
    context::{Context, Ptr},
    dialect::Dialect,
    error::Result,
    impl_attr, impl_attr_interface, input_err,
    parsable::{spaced, to_parse_result, Parsable, StateStream},
    printable::{self, Printable},
    r#type::{type_parser, TypeObj},
    verify_err,
};

use super::{attr_interfaces::TypedAttrInterface, types::IntegerType};

/// An attribute containing a string.
/// Similar to MLIR's [StringAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#stringattr).
#[derive(PartialEq, Eq, Clone)]
pub struct StringAttr(String);
impl_attr!(StringAttr, "string", "builtin");

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
        write!(f, "{} {:?}", Self::get_attr_id_static(), self.0)
    }
}

impl Verify for StringAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

impl Parsable for StringAttr {
    type Parsed = AttrObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>> {
        // An escaped charater is one that is preceded by a backslash.
        let escaped_char = combine::parser(move |parsable_state: &mut StateStream<'a>| {
            // This combine::parser() is so that we can get a position before the parsing begins.
            let position = parsable_state.position();
            let mut escaped_char = token('\\').with(any()).then(|c: char| {
                // This combine::parser() is so that we can return an error of the right type.
                // I can't get the right error type with `and_then`
                combine::parser(move |_parsable_state: &mut StateStream<'a>| {
                    // Filter out the escaped characters that we handle.
                    let result = match c {
                        '\\' => Ok('\\'),
                        '\"' => Ok('\"'),
                        _ => input_err!("Unexpected escaped character \\{}", c),
                    };
                    to_parse_result(result, position).into_result()
                })
            });
            escaped_char.parse_stream(parsable_state).into_result()
        });

        // We want to scan a double quote deliminted string with possibly escaped characters in between.
        let mut quoted_string = between(
            token('"'),
            token('"'),
            many(escaped_char.or(none_of("\"".chars()))),
        )
        .map(|str: Vec<_>| -> Box<dyn Attribute> {
            Box::new(StringAttr(str.into_iter().collect()))
        });

        quoted_string.parse_stream(state_stream)
    }
}

/// An attribute containing an integer.
/// Similar to MLIR's [IntegerAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#integerattr).
#[derive(PartialEq, Eq, Clone)]
pub struct IntegerAttr {
    ty: Ptr<TypeObj>,
    val: ApInt,
}
impl_attr!(IntegerAttr, "integer", "builtin");

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

#[derive(Error, Debug)]
#[error("value of IntegerAttr must be of IntegerType")]
struct IntegerAttrVerifyErr;

impl Verify for IntegerAttr {
    fn verify(&self, ctx: &Context) -> Result<()> {
        if !self.ty.deref(ctx).is::<IntegerType>() {
            return verify_err!(IntegerAttrVerifyErr);
        }
        Ok(())
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

impl Parsable for IntegerAttr {
    type Parsed = AttrObj;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>> {
        todo!()
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
impl_attr!(FloatAttr, "float", "builtin");

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

impl_attr_interface!(
    TypedAttrInterface for FloatAttr {
        fn get_type(&self) -> Ptr<TypeObj> {
            todo!()
        }
    }
);

impl Parsable for FloatAttr {
    type Parsed = AttrObj;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>> {
        todo!()
    }
}

/// An attribute that is a small dictionary of other attributes.
/// Implemented as a key-sorted list of key value pairs.
/// Efficient only for small number of keys.
/// Similar to MLIR's [DictionaryAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#dictionaryattr),
#[derive(PartialEq, Eq)]
pub struct SmallDictAttr(SortedVectorMap<&'static str, AttrObj>);
impl_attr!(SmallDictAttr, "small_dict", "builtin");

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

#[derive(Error, Debug)]
#[error("SmallDictAttr keys are not sorted")]
struct SmallDictAttrVerifyErr;
impl Verify for SmallDictAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        for (str1, str2) in self
            .0
            .iter()
            .map(|(&key, _)| key)
            .zip(self.0.iter().skip(1).map(|(&key, _)| key))
        {
            if str1 > str2 {
                return verify_err!(SmallDictAttrVerifyErr);
            }
        }
        Ok(())
    }
}

impl Parsable for SmallDictAttr {
    type Parsed = AttrObj;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>> {
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
impl_attr!(VecAttr, "vec", "builtin");

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

impl Parsable for VecAttr {
    type Parsed = AttrObj;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>> {
        todo!()
    }
}

/// Represent attributes that only have meaning from their existence.
/// See [UnitAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#unitattr) in MLIR.
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct UnitAttr();
impl_attr!(UnitAttr, "unit", "builtin");

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

impl Parsable for UnitAttr {
    type Parsed = AttrObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>> {
        to_parse_result(Ok(UnitAttr::create()), state_stream.position())
    }
}

/// An attribute that does nothing but hold a Type.
/// Same as MLIR's [TypeAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#typeattr).
#[derive(PartialEq, Eq, Clone)]
pub struct TypeAttr(Ptr<TypeObj>);
impl_attr!(TypeAttr, "type", "builtin");

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
        write!(f, "{} <{}>", self.get_attr_id().disp(ctx), self.0.disp(ctx))
    }
}

impl Parsable for TypeAttr {
    type Parsed = AttrObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>> {
        between(spaced(token('<')), spaced(token('>')), type_parser())
            .map(TypeAttr::create)
            .parse_stream(state_stream)
    }
}

impl Verify for TypeAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

impl_attr_interface!(
    TypedAttrInterface for TypeAttr {
        fn get_type(&self) -> Ptr<TypeObj> {
            self.0
        }
    }
);

pub fn register(dialect: &mut Dialect) {
    StringAttr::register_attr_in_dialect(dialect, StringAttr::parser_fn);
    IntegerAttr::register_attr_in_dialect(dialect, IntegerAttr::parser_fn);
    SmallDictAttr::register_attr_in_dialect(dialect, SmallDictAttr::parser_fn);
    VecAttr::register_attr_in_dialect(dialect, VecAttr::parser_fn);
    UnitAttr::register_attr_in_dialect(dialect, UnitAttr::parser_fn);
    TypeAttr::register_attr_in_dialect(dialect, TypeAttr::parser_fn);
}

#[cfg(test)]
mod tests {
    use apint::ApInt;
    use expect_test::expect;

    use crate::{
        attribute::{self, attr_cast, attr_parser},
        context::Context,
        dialects::{
            self,
            builtin::{
                attr_interfaces::TypedAttrInterface,
                attributes::{IntegerAttr, StringAttr},
                types::{IntegerType, Signedness},
            },
        },
        parsable::{self, state_stream_from_iterator},
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
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);

        let str_0_ptr = StringAttr::create("hello".to_string());
        let str_1_ptr = StringAttr::create("world".to_string());
        assert!(str_0_ptr.is::<StringAttr>() && &str_0_ptr != &str_1_ptr);
        let str_0_ptr2 = StringAttr::create("hello".to_string());
        assert!(str_0_ptr == str_0_ptr2);
        assert_eq!(str_0_ptr.disp(&ctx).to_string(), "builtin.string \"hello\"");
        assert_eq!(str_1_ptr.disp(&ctx).to_string(), "builtin.string \"world\"");
        assert_eq!(
            String::from(str_0_ptr.downcast_ref::<StringAttr>().unwrap().clone()),
            "hello",
        );
        assert_eq!(
            String::from(str_1_ptr.downcast_ref::<StringAttr>().unwrap().clone()),
            "world"
        );

        let attr_input = "builtin.string \"hello\"";
        let state_stream =
            state_stream_from_iterator(attr_input.chars(), parsable::State { ctx: &mut ctx });
        let attr = attr_parser().parse(state_stream).unwrap().0;
        assert_eq!(attr.disp(&ctx).to_string(), attr_input);

        let attr_input = "builtin.string \"hello \\\"world\\\"\"";
        let state_stream =
            state_stream_from_iterator(attr_input.chars(), parsable::State { ctx: &mut ctx });
        let attr_parsed = attr_parser().parse(state_stream).unwrap().0;
        assert_eq!(attr_parsed.disp(&ctx).to_string(), attr_input,);

        // Unsupported escaped character.
        let state_stream = state_stream_from_iterator(
            "builtin.string \"hello \\k \"".chars(),
            parsable::State { ctx: &mut ctx },
        );
        let res = attr_parser().parse(state_stream);
        let err_msg = format!("{}", res.err().unwrap());
        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 23
            Unexpected escaped character \k
        "#]];
        expected_err_msg.assert_eq(&err_msg);
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
        dialects::builtin::register(&mut ctx);

        let ty = IntegerType::get(&mut ctx, 64, Signedness::Signed);
        let ty_attr = TypeAttr::create(ty);

        let ty_interface = attr_cast::<dyn TypedAttrInterface>(&*ty_attr).unwrap();
        assert!(ty_interface.get_type() == ty);

        let ty_attr = ty_attr.disp(&ctx).to_string();
        let state_stream =
            state_stream_from_iterator(ty_attr.chars(), parsable::State { ctx: &mut ctx });
        let ty_attr_parsed = attr_parser().parse(state_stream).unwrap().0;
        assert_eq!(ty_attr_parsed.disp(&ctx).to_string(), ty_attr);
    }
}
