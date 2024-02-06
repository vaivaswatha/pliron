use apint::ApInt;
use combine::{
    any, between, many, many1, none_of,
    parser::char::{hex_digit, string},
    token, Parser,
};
use pliron_derive::def_attribute;
use sorted_vector_map::SortedVectorMap;
use thiserror::Error;

use crate::{
    attribute::{AttrObj, Attribute},
    common_traits::Verify,
    context::{Context, Ptr},
    dialect::Dialect,
    error::Result,
    impl_attr_interface, input_err,
    irfmt::printers::quoted,
    location::Located,
    parsable::{location, spaced, IntoParseResult, Parsable, ParseResult, StateStream},
    printable::{self, Printable},
    r#type::{type_parser, TypeObj, TypePtr, Typed},
    verify_err_noloc,
};

use super::{attr_interfaces::TypedAttrInterface, types::IntegerType};

/// An attribute containing a string.
/// Similar to MLIR's [StringAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#stringattr).
#[def_attribute("builtin.string")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct StringAttr(String);

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
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        quoted(&self.0).fmt(ctx, state, f)
    }
}

impl Verify for StringAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

impl Parsable for StringAttr {
    type Arg = ();
    type Parsed = AttrObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        // An escaped charater is one that is preceded by a backslash.
        let escaped_char = combine::parser(move |parsable_state: &mut StateStream<'a>| {
            // This combine::parser() is so that we can get a location before the parsing begins.
            let loc = parsable_state.loc();
            let mut escaped_char = token('\\').with(any()).then(move |c: char| {
                let loc = loc.clone();
                // This combine::parser() is so that we can return an error of the right type.
                // I can't get the right error type with `and_then`
                combine::parser(move |_parsable_state: &mut StateStream<'a>| {
                    // Filter out the escaped characters that we handle.
                    let result = match c {
                        '\\' => Ok('\\'),
                        '\"' => Ok('\"'),
                        _ => input_err!(loc.clone(), "Unexpected escaped character \\{}", c),
                    };
                    result.into_parse_result()
                })
            });
            escaped_char.parse_stream(parsable_state).into()
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

        quoted_string.parse_stream(state_stream).into()
    }
}

/// An attribute containing an integer.
/// Similar to MLIR's [IntegerAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#integerattr).
#[def_attribute("builtin.integer")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct IntegerAttr {
    ty: TypePtr<IntegerType>,
    val: ApInt,
}

impl Printable for IntegerAttr {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "<0x{:x}: {}>", self.val, self.ty.disp(ctx))
    }
}

impl Verify for IntegerAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

impl IntegerAttr {
    /// Create a new [IntegerAttr].
    pub fn create(ty: TypePtr<IntegerType>, val: ApInt) -> AttrObj {
        Box::new(IntegerAttr { ty, val })
    }
}

impl From<IntegerAttr> for ApInt {
    fn from(value: IntegerAttr) -> Self {
        value.val
    }
}

#[derive(Error, Debug)]
#[error("Type of IntegerAttr must be IntegerType")]
struct IntegerAttrTyErr;

impl Parsable for IntegerAttr {
    type Arg = ();
    type Parsed = AttrObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        between(
            token('<'),
            token('>'),
            string("0x")
                .with(many1::<String, _, _>(hex_digit()))
                .skip(token(':'))
                .and((location(), type_parser())),
        )
        .then(move |(digits, (ty_loc, ty))| {
            combine::parser(move |parsable_state: &mut StateStream<'a>| {
                let ty = TypePtr::new(ty, parsable_state.state.ctx).map_err(|_| {
                    (input_err!(ty_loc.clone(), IntegerAttrTyErr) as Result<()>).unwrap_err()
                })?;
                Ok(IntegerAttr::create(
                    ty,
                    ApInt::from_str_radix(16, digits.clone()).unwrap(),
                ))
                .into_parse_result()
            })
        })
        .parse_stream(state_stream)
        .into()
    }
}

impl Typed for IntegerAttr {
    fn get_type(&self, _ctx: &Context) -> Ptr<TypeObj> {
        self.ty.ptr()
    }
}

impl_attr_interface!(TypedAttrInterface for IntegerAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        self.ty.ptr()
    }
});

/// A dummy implementation until we have a good one.
#[derive(PartialEq, Clone, Debug)]
pub struct APFloat();

/// An attribute containing an floating point value.
/// Similar to MLIR's [FloatAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#floatattr).
/// TODO: Use rustc's APFloat.
#[def_attribute("builtin.float")]
#[derive(PartialEq, Clone, Debug)]
pub struct FloatAttr(APFloat);

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

impl Typed for FloatAttr {
    fn get_type(&self, _cfg: &Context) -> Ptr<TypeObj> {
        TypedAttrInterface::get_type(self)
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
    type Arg = ();
    type Parsed = AttrObj;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        todo!()
    }
}

/// An attribute that is a small dictionary of other attributes.
/// Implemented as a key-sorted list of key value pairs.
/// Efficient only for small number of keys.
/// Similar to MLIR's [DictionaryAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#dictionaryattr),
#[def_attribute("builtin.small_dict")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct SmallDictAttr(SortedVectorMap<&'static str, AttrObj>);

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
                return verify_err_noloc!(SmallDictAttrVerifyErr);
            }
        }
        Ok(())
    }
}

impl Parsable for SmallDictAttr {
    type Arg = ();
    type Parsed = AttrObj;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
        _argg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
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

#[def_attribute("builtin.vec")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VecAttr(pub Vec<AttrObj>);

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
    type Arg = ();
    type Parsed = AttrObj;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
        _argg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        todo!()
    }
}

/// Represent attributes that only have meaning from their existence.
/// See [UnitAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#unitattr) in MLIR.
#[def_attribute("builtin.unit")]
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct UnitAttr();

impl UnitAttr {
    pub fn create() -> AttrObj {
        Box::new(UnitAttr())
    }
}

impl Printable for UnitAttr {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "()")
    }
}

impl Verify for UnitAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

impl Parsable for UnitAttr {
    type Arg = ();
    type Parsed = AttrObj;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
        _argg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        Ok(UnitAttr::create()).into_parse_result()
    }
}

/// An attribute that does nothing but hold a Type.
/// Same as MLIR's [TypeAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#typeattr).
#[def_attribute("builtin.type")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypeAttr(Ptr<TypeObj>);

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
        write!(f, "<{}>", self.0.disp(ctx))
    }
}

impl Parsable for TypeAttr {
    type Arg = ();
    type Parsed = AttrObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        between(token('<'), token('>'), spaced(type_parser()))
            .map(TypeAttr::create)
            .parse_stream(state_stream)
            .into()
    }
}

impl Verify for TypeAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

impl Typed for TypeAttr {
    fn get_type(&self, _ctx: &Context) -> Ptr<TypeObj> {
        self.0
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
        attribute::{attr_cast, attr_parser},
        context::Context,
        dialects::{
            self,
            builtin::{
                attr_interfaces::TypedAttrInterface,
                attributes::{IntegerAttr, StringAttr},
                types::{IntegerType, Signedness},
            },
        },
        location,
        parsable::{self, state_stream_from_iterator},
        printable::Printable,
    };

    use super::{SmallDictAttr, TypeAttr, VecAttr};
    #[test]
    fn test_integer_attributes() {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);

        let i64_ty = IntegerType::get(&mut ctx, 64, Signedness::Signed);

        let int64_0_ptr = IntegerAttr::create(i64_ty, ApInt::from_i64(0));
        let int64_1_ptr = IntegerAttr::create(i64_ty, ApInt::from_i64(15));
        assert!(int64_0_ptr.is::<IntegerAttr>() && &int64_0_ptr != &int64_1_ptr);
        let int64_0_ptr2 = IntegerAttr::create(i64_ty, ApInt::from_i64(0));
        assert!(int64_0_ptr == int64_0_ptr2);
        assert_eq!(
            int64_0_ptr.disp(&ctx).to_string(),
            "builtin.integer <0x0: builtin.int<si64>>"
        );
        assert_eq!(
            int64_1_ptr.disp(&ctx).to_string(),
            "builtin.integer <0xf: builtin.int<si64>>"
        );
        assert!(
            ApInt::from(int64_0_ptr.downcast_ref::<IntegerAttr>().unwrap().clone()).is_zero()
                && ApInt::resize_to_i64(&ApInt::from(
                    int64_1_ptr.downcast_ref::<IntegerAttr>().unwrap().clone()
                )) == 15
        );

        let attr_input = "builtin.integer <0x0: builtin.unit>";
        let state_stream = state_stream_from_iterator(
            attr_input.chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let parse_err = attr_parser()
            .parse(state_stream)
            .err()
            .expect("Integer attribute with non-integer type shouldn't be parsed successfully");
        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 22
            Type of IntegerAttr must be IntegerType
        "#]];
        expected_err_msg.assert_eq(&parse_err.to_string());
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
        let state_stream = state_stream_from_iterator(
            attr_input.chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );
        let attr = attr_parser().parse(state_stream).unwrap().0;
        assert_eq!(attr.disp(&ctx).to_string(), attr_input);

        let attr_input = "builtin.string \"hello \\\"world\\\"\"";
        let state_stream = state_stream_from_iterator(
            attr_input.chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );
        let attr_parsed = attr_parser().parse(state_stream).unwrap().0;
        assert_eq!(attr_parsed.disp(&ctx).to_string(), attr_input,);

        // Unsupported escaped character.
        let state_stream = state_stream_from_iterator(
            "builtin.string \"hello \\k \"".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
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
            ("hello", hello_attr.clone()),
            ("world", world_attr.clone()),
        ]);
        let mut dict2 =
            SmallDictAttr::create(vec![("hello", StringAttr::create("hello".to_string()))]);
        let dict1_rev = SmallDictAttr::create(vec![
            ("world", world_attr.clone()),
            ("hello", hello_attr.clone()),
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

        let vec_attr = VecAttr::create(vec![hello_attr.clone(), world_attr.clone()]);
        let vec = vec_attr.downcast_ref::<VecAttr>().unwrap();
        assert!(vec.0.len() == 2 && vec.0[0] == hello_attr && vec.0[1] == world_attr);
    }

    #[test]
    fn test_type_attributes() {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);

        let ty = IntegerType::get(&mut ctx, 64, Signedness::Signed).into();
        let ty_attr = TypeAttr::create(ty);

        let ty_interface = attr_cast::<dyn TypedAttrInterface>(&*ty_attr).unwrap();
        assert!(ty_interface.get_type() == ty);

        let ty_attr = ty_attr.disp(&ctx).to_string();
        let state_stream = state_stream_from_iterator(
            ty_attr.chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );
        let ty_attr_parsed = attr_parser().parse(state_stream).unwrap().0;
        assert_eq!(ty_attr_parsed.disp(&ctx).to_string(), ty_attr);
    }
}
