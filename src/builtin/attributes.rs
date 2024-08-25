use apint::ApInt;
use combine::{
    any, between, many, many1, none_of,
    parser::char::{self, hex_digit, string},
    token, Parser,
};
use pliron_derive::{attr_interface_impl, def_attribute};

use crate::{
    attribute::{AttrObj, Attribute, AttributeDict},
    common_traits::Verify,
    context::{Context, Ptr},
    identifier::Identifier,
    impl_verify_succ, input_err,
    irfmt::{
        parsers::{delimited_list_parser, spaced, type_parser},
        printers::{list_with_sep, quoted},
    },
    location::Located,
    parsable::{IntoParseResult, Parsable, ParseResult, StateStream},
    printable::{self, Printable},
    r#type::{TypeObj, TypePtr, Typed},
    result::Result,
};

use super::{attr_interfaces::TypedAttrInterface, types::IntegerType};

#[def_attribute("builtin.identifier")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct IdentifierAttr(Identifier);

impl IdentifierAttr {
    /// Create a new [IdentifierAttr]
    pub fn new(value: Identifier) -> Self {
        IdentifierAttr(value)
    }
}

impl_verify_succ!(IdentifierAttr);

impl Printable for IdentifierAttr {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.0.fmt(ctx, state, f)
    }
}

impl From<IdentifierAttr> for Identifier {
    fn from(value: IdentifierAttr) -> Self {
        value.0
    }
}

impl Parsable for IdentifierAttr {
    type Arg = ();

    type Parsed = IdentifierAttr;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        Identifier::parser(arg)
            .parse_stream(state_stream)
            .map(IdentifierAttr::new)
            .into_result()
    }
}

/// An attribute containing a string.
/// Similar to MLIR's [StringAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#stringattr).
#[def_attribute("builtin.string")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct StringAttr(String);

impl StringAttr {
    /// Create a new [StringAttr].
    pub fn new(value: String) -> Self {
        StringAttr(value)
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

impl_verify_succ!(StringAttr);

impl Parsable for StringAttr {
    type Arg = ();
    type Parsed = Self;

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
        .map(|str: Vec<_>| StringAttr(str.into_iter().collect()));

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

impl_verify_succ!(IntegerAttr);

impl IntegerAttr {
    /// Create a new [IntegerAttr].
    pub fn new(ty: TypePtr<IntegerType>, val: ApInt) -> Self {
        IntegerAttr { ty, val }
    }
}

impl From<IntegerAttr> for ApInt {
    fn from(value: IntegerAttr) -> Self {
        value.val
    }
}

impl Parsable for IntegerAttr {
    type Arg = ();
    type Parsed = Self;

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
                .and(TypePtr::<IntegerType>::parser(())),
        )
        .parse_stream(state_stream)
        .map(|(digits, ty)| {
            IntegerAttr::new(ty, ApInt::from_str_radix(16, digits.clone()).unwrap())
        })
        .into_result()
    }
}

impl Typed for IntegerAttr {
    fn get_type(&self, _ctx: &Context) -> Ptr<TypeObj> {
        self.ty.into()
    }
}

#[attr_interface_impl]
impl TypedAttrInterface for IntegerAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        self.ty.into()
    }
}

/// A dummy implementation until we have a good one.
#[derive(PartialEq, Clone, Debug)]
pub struct APFloat;

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
    pub fn new(value: APFloat) -> Self {
        FloatAttr(value)
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

#[attr_interface_impl]
impl TypedAttrInterface for FloatAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        todo!()
    }
}

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

/// An attribute that is a dictionary of other attributes.
/// Similar to MLIR's [DictionaryAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#dictionaryattr),
#[def_attribute("builtin.dict")]
#[derive(PartialEq, Clone, Eq, Debug)]
pub struct DictAttr(AttributeDict);

impl Printable for DictAttr {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{}", self.0.disp(ctx))
    }
}

impl_verify_succ!(DictAttr);

impl Parsable for DictAttr {
    type Arg = ();
    type Parsed = Self;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
        _argg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        todo!()
    }
}

impl DictAttr {
    /// Create a new [DictAttr].
    pub fn new(value: Vec<(Identifier, AttrObj)>) -> Self {
        let mut dict = AttributeDict::default();
        for (name, val) in value {
            dict.0.insert(name, val);
        }
        DictAttr(dict)
    }

    /// Add an entry to the dictionary.
    pub fn insert(&mut self, key: &Identifier, val: AttrObj) {
        self.0 .0.insert(key.clone(), val);
    }

    /// Remove an entry from the dictionary.
    pub fn remove(&mut self, key: &Identifier) {
        self.0 .0.remove(key);
    }

    /// Lookup a name in the dictionary.
    pub fn lookup<'a>(&'a self, key: &Identifier) -> Option<&'a AttrObj> {
        self.0 .0.get(key)
    }

    /// Lookup a name in the dictionary, get a mutable reference.
    pub fn lookup_mut<'a>(&'a mut self, key: &Identifier) -> Option<&'a mut AttrObj> {
        self.0 .0.get_mut(key)
    }
}

/// A vector of other attributes.
#[def_attribute("builtin.vec")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VecAttr(pub Vec<AttrObj>);

impl VecAttr {
    pub fn new(value: Vec<AttrObj>) -> Self {
        VecAttr(value)
    }
}

impl Printable for VecAttr {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(
            f,
            "[{}]",
            list_with_sep(&self.0, printable::ListSeparator::Char(',')).disp(ctx)
        )
    }
}

impl Verify for VecAttr {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.0.iter().try_for_each(|elm| elm.verify(ctx))
    }
}

impl Parsable for VecAttr {
    type Arg = ();
    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        delimited_list_parser('[', ']', ',', AttrObj::parser(arg))
            .parse_stream(state_stream)
            .map(VecAttr::new)
            .into_result()
    }
}

/// Represent attributes that only have meaning from their existence.
/// See [UnitAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#unitattr) in MLIR.
#[def_attribute("builtin.unit")]
#[derive(PartialEq, Eq, Clone, Copy, Debug, Default)]
pub struct UnitAttr;

impl UnitAttr {
    pub fn new() -> Self {
        UnitAttr
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
impl_verify_succ!(UnitAttr);

impl Parsable for UnitAttr {
    type Arg = ();
    type Parsed = Self;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
        _argg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        Ok(UnitAttr::new()).into_parse_result()
    }
}

/// An attribute that does nothing but hold a Type.
/// Same as MLIR's [TypeAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#typeattr).
#[def_attribute("builtin.type")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypeAttr(Ptr<TypeObj>);

impl TypeAttr {
    pub fn new(ty: Ptr<TypeObj>) -> Self {
        TypeAttr(ty)
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
    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        between(token('<'), token('>'), spaced(type_parser()))
            .map(TypeAttr::new)
            .parse_stream(state_stream)
            .into()
    }
}

impl_verify_succ!(TypeAttr);

impl Typed for TypeAttr {
    fn get_type(&self, _ctx: &Context) -> Ptr<TypeObj> {
        self.0
    }
}

#[attr_interface_impl]
impl TypedAttrInterface for TypeAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        self.0
    }
}

pub fn register(ctx: &mut Context) {
    IdentifierAttr::register_attr_in_dialect(ctx, IdentifierAttr::parser_fn);
    StringAttr::register_attr_in_dialect(ctx, StringAttr::parser_fn);
    IntegerAttr::register_attr_in_dialect(ctx, IntegerAttr::parser_fn);
    DictAttr::register_attr_in_dialect(ctx, DictAttr::parser_fn);
    VecAttr::register_attr_in_dialect(ctx, VecAttr::parser_fn);
    UnitAttr::register_attr_in_dialect(ctx, UnitAttr::parser_fn);
    TypeAttr::register_attr_in_dialect(ctx, TypeAttr::parser_fn);
}

#[cfg(test)]
mod tests {
    use apint::ApInt;
    use expect_test::expect;

    use crate::{
        attribute::{attr_cast, AttrObj},
        builtin::{
            self,
            attr_interfaces::TypedAttrInterface,
            attributes::{IntegerAttr, StringAttr},
            types::{IntegerType, Signedness},
        },
        context::Context,
        identifier::Identifier,
        irfmt::parsers::attr_parser,
        location,
        parsable::{self, state_stream_from_iterator},
        printable::Printable,
    };

    use super::{DictAttr, TypeAttr, VecAttr};
    #[test]
    fn test_integer_attributes() {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);

        let i64_ty = IntegerType::get(&mut ctx, 64, Signedness::Signed);

        let int64_0_ptr: AttrObj = IntegerAttr::new(i64_ty, ApInt::from_i64(0)).into();
        let int64_1_ptr: AttrObj = IntegerAttr::new(i64_ty, ApInt::from_i64(15)).into();
        assert!(int64_0_ptr.is::<IntegerAttr>() && &int64_0_ptr != &int64_1_ptr);
        let int64_0_ptr2: AttrObj = IntegerAttr::new(i64_ty, ApInt::from_i64(0)).into();
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
            Expected type builtin.int, but found builtin.unit
        "#]];
        expected_err_msg.assert_eq(&parse_err.to_string());
    }

    #[test]
    fn test_string_attributes() {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);

        let str_0_ptr: AttrObj = StringAttr::new("hello".to_string()).into();
        let str_1_ptr: AttrObj = StringAttr::new("world".to_string()).into();
        assert!(str_0_ptr.is::<StringAttr>() && &str_0_ptr != &str_1_ptr);
        let str_0_ptr2: AttrObj = StringAttr::new("hello".to_string()).into();
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
        let hello_attr: AttrObj = StringAttr::new("hello".to_string()).into();
        let world_attr: AttrObj = StringAttr::new("world".to_string()).into();

        let hello_id: Identifier = "hello".try_into().unwrap();
        let world_id: Identifier = "world".try_into().unwrap();

        let mut dict1: AttrObj = DictAttr::new(vec![
            (hello_id.clone(), hello_attr.clone()),
            (world_id.clone(), world_attr.clone()),
        ])
        .into();
        let mut dict2 = DictAttr::new(vec![(
            hello_id.clone(),
            StringAttr::new("hello".to_string()).into(),
        )])
        .into();
        let dict1_rev = DictAttr::new(vec![
            (world_id.clone(), world_attr.clone()),
            (hello_id.clone(), hello_attr.clone()),
        ])
        .into();
        assert!(&dict1 != &dict2);
        assert!(dict1 == dict1_rev);

        let dict1_attr = dict1.as_mut().downcast_mut::<DictAttr>().unwrap();
        let dict2_attr = dict2.as_mut().downcast_mut::<DictAttr>().unwrap();
        assert!(dict1_attr.lookup(&hello_id).unwrap() == &hello_attr);
        assert!(dict1_attr.lookup(&world_id).unwrap() == &world_attr);
        assert!(dict1_attr
            .lookup(&"hello_world".try_into().unwrap())
            .is_none());
        dict2_attr.insert(&world_id, world_attr);
        assert!(dict1_attr == dict2_attr);

        dict1_attr.remove(&hello_id);
        dict2_attr.remove(&hello_id);
        assert!(&dict1 == &dict2);
    }

    #[test]
    fn test_vec_attributes() {
        let hello_attr: AttrObj = StringAttr::new("hello".to_string()).into();
        let world_attr: AttrObj = StringAttr::new("world".to_string()).into();

        let vec_attr: AttrObj = VecAttr::new(vec![hello_attr.clone(), world_attr.clone()]).into();
        let vec = vec_attr.downcast_ref::<VecAttr>().unwrap();
        assert!(vec.0.len() == 2 && vec.0[0] == hello_attr && vec.0[1] == world_attr);
    }

    #[test]
    fn test_type_attributes() {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);

        let ty = IntegerType::get(&mut ctx, 64, Signedness::Signed).into();
        let ty_attr: AttrObj = TypeAttr::new(ty).into();

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
