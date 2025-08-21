use std::hash::{Hash, Hasher};

use combine::{
    Parser, between, many1,
    parser::char::{char, digit, spaces},
    token,
};
use pliron::derive::{attr_interface_impl, def_attribute};
use pliron_derive::format_attribute;
use rustc_apfloat::Float;
use thiserror::Error;

use crate::{
    attribute::{AttrObj, Attribute, AttributeDict},
    builtin::attr_interfaces::FloatAttr,
    common_traits::Verify,
    context::{Context, Ptr},
    identifier::Identifier,
    impl_verify_succ, input_err,
    irfmt::{
        parsers::{quoted_string_parser, spaced},
        printers::quoted,
    },
    location::Located,
    parsable::{IntoParseResult, Parsable, ParseResult, StateStream},
    printable::{self, Printable},
    result::Result,
    r#type::{TypeObj, TypePtr, Typed},
    utils::{
        apfloat::{self, double_to_f64, f32_to_single, f64_to_double, single_to_f32},
        apint::APInt,
    },
    verify_err_noloc,
};

use super::{
    attr_interfaces::TypedAttrInterface,
    types::{IntegerType, Signedness},
};

#[def_attribute("builtin.identifier")]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
#[format_attribute("$0")]
pub struct IdentifierAttr(Identifier);

impl IdentifierAttr {
    /// Create a new [IdentifierAttr]
    pub fn new(value: Identifier) -> Self {
        IdentifierAttr(value)
    }
}

impl_verify_succ!(IdentifierAttr);

impl From<IdentifierAttr> for Identifier {
    fn from(value: IdentifierAttr) -> Self {
        value.0
    }
}

/// An attribute containing a string.
/// Similar to MLIR's [StringAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#stringattr).
#[def_attribute("builtin.string")]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
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
        quoted_string_parser()
            .map(StringAttr)
            .parse_stream(state_stream)
            .into_result()
    }
}

/// An attribute containing an integer.
/// Similar to MLIR's [IntegerAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#integerattr).
#[def_attribute("builtin.integer")]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct IntegerAttr {
    ty: TypePtr<IntegerType>,
    val: APInt,
}

impl Printable for IntegerAttr {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        let ty = &*self.ty.deref(ctx);
        write!(
            f,
            "<{}: {}>",
            self.val
                .to_string_decimal(ty.get_signedness() == Signedness::Signed),
            ty.disp(ctx)
        )
    }
}

#[derive(Debug, Error)]
#[error("The bitwidth type does not match the bitwidth of the value.")]
pub struct IntegerAttrBitwidthErr;

impl Verify for IntegerAttr {
    fn verify(&self, ctx: &Context) -> Result<()> {
        if self.ty.deref(ctx).get_width() as usize != self.val.bw() {
            return verify_err_noloc!(IntegerAttrBitwidthErr);
        }
        Ok(())
    }
}

impl IntegerAttr {
    /// Create a new [IntegerAttr].
    pub fn new(ty: TypePtr<IntegerType>, val: APInt) -> Self {
        IntegerAttr { ty, val }
    }

    /// Get the value of the attribute.
    pub fn get_value(&self) -> APInt {
        self.val.clone()
    }

    /// Get the type of the attribute.
    pub fn get_type(&self) -> TypePtr<IntegerType> {
        self.ty
    }
}

impl From<IntegerAttr> for APInt {
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
            spaces()
                .with(many1::<String, _, _>(digit().or(char('-').or(char('+')))))
                .skip(spaced(token(':')))
                .and(IntegerType::parser(())),
        )
        .then(|(digits, ty)| {
            combine::parser(move |state_stream: &mut StateStream<'a>| {
                let ty_ref = &*ty.deref(state_stream.state.ctx);
                let apint = match APInt::from_str(&digits, ty_ref.get_width() as usize, 10) {
                    Ok(val) => Ok(val).into_parse_result(),
                    Err(err) => input_err!(state_stream.loc(), "{}", err).into_parse_result(),
                }?;
                Ok(IntegerAttr::new(ty, apint.0)).into_parse_result()
            })
        })
        .parse_stream(state_stream)
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

#[def_attribute("builtin.single")]
#[derive(PartialEq, Clone, Debug)]
#[format_attribute("$0")]
/// An attribute that is a single-precision floating-point number.
pub struct FPSingleAttr(pub apfloat::Single);
impl_verify_succ!(FPSingleAttr);

impl From<f32> for FPSingleAttr {
    fn from(value: f32) -> Self {
        FPSingleAttr(f32_to_single(value))
    }
}

impl From<FPSingleAttr> for f32 {
    fn from(value: FPSingleAttr) -> Self {
        single_to_f32(value.0)
    }
}

impl Hash for FPSingleAttr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

#[attr_interface_impl]
impl FloatAttr for FPSingleAttr {
    fn get_inner(&self) -> &dyn apfloat::DynFloat {
        &self.0
    }

    fn build_from(&self, df: Box<dyn apfloat::DynFloat>) -> Box<dyn FloatAttr> {
        let df = df
            .downcast::<apfloat::Single>()
            .expect("Expected a Single precision float");
        Box::new(FPSingleAttr(*df))
    }
}

#[def_attribute("builtin.double")]
#[derive(PartialEq, Clone, Debug)]
#[format_attribute("$0")]
/// An attribute that is a double-precision floating-point number.
pub struct FPDoubleAttr(pub apfloat::Double);
impl_verify_succ!(FPDoubleAttr);

impl From<f64> for FPDoubleAttr {
    fn from(value: f64) -> Self {
        FPDoubleAttr(f64_to_double(value))
    }
}

impl From<FPDoubleAttr> for f64 {
    fn from(value: FPDoubleAttr) -> Self {
        double_to_f64(value.0)
    }
}

impl Hash for FPDoubleAttr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

#[attr_interface_impl]
impl FloatAttr for FPDoubleAttr {
    fn get_inner(&self) -> &dyn apfloat::DynFloat {
        &self.0
    }

    fn build_from(&self, df: Box<dyn apfloat::DynFloat>) -> Box<dyn FloatAttr> {
        let df = df
            .downcast::<apfloat::Double>()
            .expect("Expected a Double precision float");
        Box::new(FPDoubleAttr(*df))
    }
}

/// An attribute that is a dictionary of other attributes.
/// Similar to MLIR's [DictionaryAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#dictionaryattr),
#[def_attribute("builtin.dict")]
#[derive(PartialEq, Clone, Eq, Debug, Hash)]
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
        AttributeDict::parser(())
            .map(DictAttr)
            .parse_stream(_state_stream)
            .into_result()
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
        self.0.0.insert(key.clone(), val);
    }

    /// Remove an entry from the dictionary.
    pub fn remove(&mut self, key: &Identifier) {
        self.0.0.remove(key);
    }

    /// Lookup a name in the dictionary.
    pub fn lookup<'a>(&'a self, key: &Identifier) -> Option<&'a AttrObj> {
        self.0.0.get(key)
    }

    /// Lookup a name in the dictionary, get a mutable reference.
    pub fn lookup_mut<'a>(&'a mut self, key: &Identifier) -> Option<&'a mut AttrObj> {
        self.0.0.get_mut(key)
    }
}

/// A vector of other attributes.
#[def_attribute("builtin.vec")]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
#[format_attribute("`[` vec($0, CharSpace(`,`)) `]`")]
pub struct VecAttr(pub Vec<AttrObj>);

impl VecAttr {
    pub fn new(value: Vec<AttrObj>) -> Self {
        VecAttr(value)
    }
}

impl Verify for VecAttr {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.0.iter().try_for_each(|elm| elm.verify(ctx))
    }
}

/// Represent attributes that only have meaning from their existence.
/// See [UnitAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#unitattr) in MLIR.
#[def_attribute("builtin.unit")]
#[format_attribute]
#[derive(PartialEq, Eq, Clone, Copy, Debug, Default, Hash)]
pub struct UnitAttr;

impl UnitAttr {
    pub fn new() -> Self {
        UnitAttr
    }
}

impl_verify_succ!(UnitAttr);

/// An attribute that does nothing but hold a Type.
/// Same as MLIR's [TypeAttr](https://mlir.llvm.org/docs/Dialects/Builtin/#typeattr).
#[def_attribute("builtin.type")]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
#[format_attribute("$0")]
pub struct TypeAttr(Ptr<TypeObj>);

impl TypeAttr {
    pub fn new(ty: Ptr<TypeObj>) -> Self {
        TypeAttr(ty)
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

#[def_attribute("builtin.operand_segment_sizes")]
#[format_attribute("`[` vec($0, CharSpace(`,`)) `]`")]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct OperandSegmentSizesAttr(pub Vec<u32>);
impl_verify_succ!(OperandSegmentSizesAttr);

pub fn register(ctx: &mut Context) {
    IdentifierAttr::register_attr_in_dialect(ctx, IdentifierAttr::parser_fn);
    StringAttr::register_attr_in_dialect(ctx, StringAttr::parser_fn);
    IntegerAttr::register_attr_in_dialect(ctx, IntegerAttr::parser_fn);
    DictAttr::register_attr_in_dialect(ctx, DictAttr::parser_fn);
    VecAttr::register_attr_in_dialect(ctx, VecAttr::parser_fn);
    UnitAttr::register_attr_in_dialect(ctx, UnitAttr::parser_fn);
    TypeAttr::register_attr_in_dialect(ctx, TypeAttr::parser_fn);
    OperandSegmentSizesAttr::register_attr_in_dialect(ctx, OperandSegmentSizesAttr::parser_fn);

    FPSingleAttr::register_attr_in_dialect(ctx, FPSingleAttr::parser_fn);
    FPDoubleAttr::register_attr_in_dialect(ctx, FPDoubleAttr::parser_fn);
}

#[cfg(test)]
mod tests {
    use awint::bw;
    use expect_test::expect;

    use crate::{
        attribute::{AttrObj, attr_cast},
        builtin::{
            self,
            attr_interfaces::TypedAttrInterface,
            attributes::{
                FPDoubleAttr, FPSingleAttr, IntegerAttr, OperandSegmentSizesAttr, StringAttr,
            },
            types::{IntegerType, Signedness},
        },
        context::Context,
        identifier::Identifier,
        irfmt::parsers::attr_parser,
        location,
        parsable::{self, state_stream_from_iterator},
        printable::Printable,
        utils::apint::APInt,
    };

    use super::{DictAttr, TypeAttr, VecAttr};
    #[test]
    fn test_integer_attributes() {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);

        let i64_ty = IntegerType::get(&mut ctx, 64, Signedness::Signed);

        let int64_0_ptr: AttrObj = IntegerAttr::new(i64_ty, APInt::from_i64(0, bw(64))).into();
        let int64_1_ptr: AttrObj = IntegerAttr::new(i64_ty, APInt::from_i64(15, bw(64))).into();
        assert!(int64_0_ptr.is::<IntegerAttr>() && &int64_0_ptr != &int64_1_ptr);
        let int64_0_ptr2: AttrObj = IntegerAttr::new(i64_ty, APInt::from_i64(0, bw(64))).into();
        assert!(int64_0_ptr == int64_0_ptr2);
        assert_eq!(
            int64_0_ptr.disp(&ctx).to_string(),
            "builtin.integer <0: si64>"
        );
        assert_eq!(
            int64_1_ptr.disp(&ctx).to_string(),
            "builtin.integer <15: si64>"
        );
        assert!(
            APInt::from(int64_0_ptr.downcast_ref::<IntegerAttr>().unwrap().clone()).is_zero()
                && APInt::to_i64(&APInt::from(
                    int64_1_ptr.downcast_ref::<IntegerAttr>().unwrap().clone()
                )) == 15
        );

        let attr_input = "builtin.integer <0: builtin.unit>";
        let state_stream = state_stream_from_iterator(
            attr_input.chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let parse_err = attr_parser()
            .parse(state_stream)
            .err()
            .expect("Integer attribute with non-integer type shouldn't be parsed successfully");
        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 21
            Unexpected `b`
            Expected whitespaces, si, ui, i or whitespace
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
        assert!(
            dict1_attr
                .lookup(&"hello_world".try_into().unwrap())
                .is_none()
        );
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

    #[test]
    fn test_operand_segment_sizes_attr() {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);

        let sizes = vec![1, 2, 3];
        let attr: AttrObj = OperandSegmentSizesAttr(sizes.clone()).into();
        let attr_parsed = attr.downcast_ref::<OperandSegmentSizesAttr>().unwrap();
        assert_eq!(attr_parsed.0, sizes);

        let attr_disp = attr.disp(&ctx).to_string();
        let state_stream = state_stream_from_iterator(
            attr_disp.chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );
        let attr_parsed = attr_parser().parse(state_stream).unwrap().0;
        assert_eq!(attr_parsed.disp(&ctx).to_string(), attr_disp);
        let attr_parsed = attr_parsed
            .downcast_ref::<OperandSegmentSizesAttr>()
            .unwrap();
        assert_eq!(attr_parsed.0, sizes);
    }

    #[test]
    fn test_floating_point_attributes() {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);

        // Single precision float
        let single_attr: AttrObj = FPSingleAttr::from(3.14).into();
        let single_attr2: AttrObj = FPSingleAttr::from(2.71).into();

        assert!(single_attr.is::<FPSingleAttr>());
        assert_ne!(&single_attr, &single_attr2);

        let single_attr = *single_attr.downcast::<FPSingleAttr>().unwrap();
        assert_eq!(f32::from(single_attr.clone()), 3.14);

        let single_attr2 = *single_attr2.downcast::<FPSingleAttr>().unwrap();
        // Perform addition
        let sum: f32 = f32::from(single_attr.clone()) + f32::from(single_attr2);
        assert!((sum - 5.85).abs() < 1e-6);

        // Double precision float
        let double_attr: AttrObj = FPDoubleAttr::from(6.28).into();
        let double_attr2: AttrObj = FPDoubleAttr::from(1.414).into();

        assert!(double_attr.is::<FPDoubleAttr>());
        assert_ne!(&double_attr, &double_attr2);

        let double_attr = *double_attr.downcast::<FPDoubleAttr>().unwrap();
        assert_eq!(f64::from(double_attr.clone()), 6.28);

        let double_attr2 = *double_attr2.downcast::<FPDoubleAttr>().unwrap();
        // Perform multiplication
        let product: f64 = f64::from(double_attr) * f64::from(double_attr2);
        dbg!(product);
        assert!((product - 8.87992).abs() < 1e-6);
    }
}
