#![allow(unused)]
#![allow(dead_code)]

use super::*;

use crate::{
    attribute::{attr_cast, Attribute},
    dialects::builtin::attr_interfaces::TypedAttrInterface,
    identifier::Identifier,
    impl_attr_interface,
    irfmt::parsers::AsmParser,
    location::{self, Location},
    op::{Op, OpObj},
    operation::Operation,
    parsable::{self, state_stream_from_iterator},
    r#type::Type,
    r#type::TypePtr,
};
use apint::ApInt;
use combine::{eof, error::Commit};
use pliron_derive::{
    def_attribute, def_op, def_type, NotParsableAttribute, NotParsableType, Parsable, Printable,
};

use crate::{
    attribute::AttrObj,
    common_traits::Verify,
    context::Ptr,
    error::Result,
    irfmt::parsers,
    parsable::{Parsable, ParseResult, StateStream},
    r#type::TypeObj,
};

fn register_dialect(ctx: &mut Context) {
    let mut dialect = crate::dialect::Dialect::new(crate::dialect::DialectName::new("testing"));
    SimpleType::register_type_in_dialect(&mut dialect, SimpleType::parser_fn);
    IntegerType::register_type_in_dialect(&mut dialect, IntegerType::parser_fn);
    FunctionType::register_type_in_dialect(&mut dialect, FunctionType::parser_fn);
    VecType::register_type_in_dialect(&mut dialect, VecType::parser_fn);
    StringAttr::register_attr_in_dialect(&mut dialect, StringAttr::parser_fn);
    IntegerAttr::register_attr_in_dialect(&mut dialect, IntegerAttr::parser_fn);
    UnitAttr::register_attr_in_dialect(&mut dialect, UnitAttr::parser_fn);
    VecAttr::register_attr_in_dialect(&mut dialect, VecAttr::parser_fn);
    ConstantOp::register(ctx, &mut dialect, ConstantOp::parser_fn);
    dialect.register(ctx);
}

#[def_type("testing.simple_type")]
#[derive(Hash, PartialEq, Eq, Debug, Printable, Parsable)]
#[ir_format = ""]
pub struct SimpleType {}
impl SimpleType {
    /// Get or create a new simple type.
    pub fn get(ctx: &mut Context) -> TypePtr<Self> {
        Type::register_instance(SimpleType {}, ctx)
    }
}
impl Verify for SimpleType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

#[def_type("testing.int")]
#[derive(Hash, PartialEq, Eq, Debug, Printable, Parsable)]
//#[ir_format = "`int <` `sign=` $sign `, width=` $width `, align=` $align `>`"]
//#[ir_format = "`int <` params `>`"]
//#[ir_format = "`int <` struct(params) `>`"]
//#[ir_format = "`int <` struct($width, $sign) `>`"]
#[ir_format = "$width `<` $align `,` $sign `>`"]
pub struct IntegerType {
    width: u32,
    sign: bool,
    align: u32,
}
impl IntegerType {
    fn get(ctx: &mut Context, width: u32, sign: bool, align: u32) -> TypePtr<Self> {
        Type::register_instance(Self { sign, width, align }, ctx)
    }

    /// Get, if it already exists, an integer type.
    pub fn get_existing(
        ctx: &Context,
        width: u32,
        sign: bool,
        align: u32,
    ) -> Option<TypePtr<Self>> {
        Type::get_instance(Self { width, sign, align }, ctx)
    }
}
impl Verify for IntegerType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

#[def_type("testing.vec")]
#[derive(Hash, PartialEq, Eq, Debug, Printable, NotParsableType)]
// #[ir_format = "`vec [` qualified($elem) `]` "]
// #[ir_format = "`vec ` qualifier($elem) ` <` $elem `>` "]
#[ir_format = "` ` $elem"]
pub struct VecType {
    elem: Ptr<TypeObj>,
}
impl VecType {
    fn get(ctx: &mut Context, elem: Ptr<TypeObj>) -> TypePtr<Self> {
        Type::register_instance(Self { elem }, ctx)
    }
}
impl Verify for VecType {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.elem.verify(ctx)?;
        Ok(())
    }
}

#[def_type("testing.function")]
#[derive(Hash, PartialEq, Debug, Eq, Printable)]
// #[ir_format = "functional_type($inputs, $results)"]
#[ir_format = "`(` $inputs `) -> (` $results `)`"]
pub struct FunctionType {
    inputs: Vec<Ptr<TypeObj>>,
    results: Vec<Ptr<TypeObj>>,
}
impl Verify for FunctionType {
    fn verify(&self, ctx: &Context) -> Result<()> {
        for ty in &self.inputs {
            ty.verify(ctx)?;
        }
        for ty in &self.results {
            ty.verify(ctx)?;
        }
        Ok(())
    }
}
impl ::pliron::parsable::Parsable for FunctionType {
    type Arg = ();
    type Parsed = TypePtr<Self>;
    fn parse<'a>(
        _state_stream: &mut ::pliron::parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> ::pliron::parsable::ParseResult<'a, Self::Parsed> {
        todo!()
    }
}

impl FunctionType {
    pub fn get(
        ctx: &mut Context,
        inputs: Vec<Ptr<TypeObj>>,
        results: Vec<Ptr<TypeObj>>,
    ) -> TypePtr<Self> {
        Type::register_instance(FunctionType { inputs, results }, ctx)
    }
}

#[def_attribute("testing.int")]
#[derive(PartialEq, Eq, Debug, Clone, Printable)]
#[ir_format = "format(`0x{:x}`, $val) `: ` $ty"]
pub struct IntegerAttr {
    ty: TypePtr<IntegerType>,
    val: ApInt,
}
impl IntegerAttr {
    pub fn create(ty: TypePtr<IntegerType>, val: ApInt) -> AttrObj {
        Box::new(IntegerAttr { ty, val })
    }
}
impl Verify for IntegerAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl ::pliron::parsable::Parsable for IntegerAttr {
    type Arg = ();
    type Parsed = ::pliron::attribute::AttrObj;
    fn parse<'a>(
        _state_stream: &mut ::pliron::parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> ::pliron::parsable::ParseResult<'a, Self::Parsed> {
        todo!()
    }
}
impl_attr_interface!(TypedAttrInterface for IntegerAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        self.ty.to_ptr()
    }
});

#[def_attribute("testing.string")]
#[derive(PartialEq, Eq, Debug, Clone, Printable, NotParsableAttribute)]
#[ir_format = "quoted($0)"]
struct StringAttr(String);
impl Verify for StringAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

#[def_attribute("testing.unit")]
#[derive(PartialEq, Eq, Debug, Clone, Printable, NotParsableAttribute)]
#[ir_format = "`()`"]
pub struct UnitAttr();
impl UnitAttr {
    pub fn create() -> AttrObj {
        Box::new(UnitAttr())
    }
}

impl Verify for UnitAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

#[def_attribute("testing.vec")]
#[derive(Clone, PartialEq, Debug, Eq, Printable, NotParsableAttribute)]
pub struct VecAttr(pub Vec<AttrObj>);
impl Verify for VecAttr {
    fn verify(&self, ctx: &Context) -> Result<()> {
        for attr in &self.0 {
            attr.verify(ctx)?;
        }
        Ok(())
    }
}

#[def_op("testing.const")]
#[derive(Printable)]
struct ConstantOp;
impl ConstantOp {
    /// Attribute key for the constant value.
    pub const ATTR_KEY_VALUE: &'static str = "constant.value";

    /// Get the constant value that this Op defines.
    pub fn get_value(&self, ctx: &Context) -> AttrObj {
        let op = self.get_operation().deref(ctx);
        op.attributes.get(Self::ATTR_KEY_VALUE).unwrap().clone()
    }

    /// Create a new [ConstantOp]. The underlying [Operation] is not linked to a [BasicBlock].
    pub fn new_unlinked(ctx: &mut Context, value: AttrObj) -> Self {
        let result_type = attr_cast::<dyn TypedAttrInterface>(&*value)
            .expect("ConstantOp const value must provide TypedAttrInterface")
            .get_type();
        let op = Operation::new(ctx, Self::get_opid_static(), vec![result_type], vec![], 0);
        op.deref_mut(ctx)
            .attributes
            .insert(Self::ATTR_KEY_VALUE, value);
        Self { op }
    }
}
impl Verify for ConstantOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl Parsable for ConstantOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        todo!()
    }
}

#[test]
fn print_simple_type() {
    let mut ctx = Context::new();
    register_dialect(&mut ctx);

    let got = SimpleType::get(&mut ctx).disp(&ctx).to_string();
    assert_eq!(got, "testing.simple_type");
}

#[test]
fn print_integer_type() {
    let mut ctx = Context::new();
    register_dialect(&mut ctx);

    let ty = IntegerType::get(&mut ctx, 32, true, 8);
    let got = ty.disp(&ctx).to_string();
    assert_eq!(got, "testing.int32<8,true>");
}

#[test]
#[ignore]
fn parse_integer_type() {
    use combine::Parser;

    let mut ctx = Context::new();
    register_dialect(&mut ctx);

    // TODO:
    let a = "testing.int<sign=true, width=32, align=8>".to_string();
    let mut state_stream = state_stream_from_iterator(
        a.chars(),
        parsable::State::new(&mut ctx, location::Source::InMemory),
    );

    let _ = parsers::type_header()
        .parse_next(&mut state_stream)
        .unwrap();
    let res = IntegerType::parser(())
        .and(eof())
        .parse(state_stream)
        .unwrap()
        .0
         .0;

    assert!(res == IntegerType::get_existing(&ctx, 32, true, 8).unwrap());
}

#[test]
fn print_vec_type() {
    let mut ctx = Context::new();
    register_dialect(&mut ctx);

    let i32_ty = IntegerType::get(&mut ctx, 32, true, 4);
    let vec_ty = VecType::get(&mut ctx, i32_ty.to_ptr());
    let got = vec_ty.disp(&ctx).to_string();
    assert_eq!(got, "testing.vec testing.int32<4,true>");
}

#[test]
fn print_function() {
    let mut ctx = Context::new();
    register_dialect(&mut ctx);

    let i32_ty = IntegerType::get(&mut ctx, 32, true, 4).to_ptr();
    let u64_ty = IntegerType::get(&mut ctx, 32, false, 8).to_ptr();
    let func_ty = FunctionType::get(&mut ctx, vec![i32_ty, i32_ty], vec![u64_ty]);

    let got = func_ty.disp(&ctx).to_string();
    assert_eq!(
        got,
        "testing.function(testing.int32<4,true>,testing.int32<4,true>) -> (testing.int32<8,false>)"
    );
}

#[test]
fn print_unit_attr() {
    let mut ctx = Context::new();
    register_dialect(&mut ctx);

    let attr = UnitAttr();
    let got = attr.disp(&ctx).to_string();
    assert_eq!(got, "()");
}

#[test]
fn print_string_attr() {
    let mut ctx = Context::new();
    register_dialect(&mut ctx);

    let attr = StringAttr("hello".to_string());
    let got = attr.disp(&ctx).to_string();
    assert_eq!(got, r#""hello""#);
}

#[test]
fn print_int_attr() {
    let mut ctx = Context::new();
    register_dialect(&mut ctx);

    let ty = IntegerType::get(&mut ctx, 32, true, 8);
    let attr = IntegerAttr::create(ty, ApInt::from(42));
    let got = attr.disp(&ctx).to_string();
    assert_eq!(got, "testing.int 0x2a: testing.int32<8,true>");
}

#[test]
fn print_vec_attr() {
    let mut ctx = Context::new();
    register_dialect(&mut ctx);

    let vec_attr = VecAttr(vec![UnitAttr::create(), UnitAttr::create()]);
    let got = vec_attr.disp(&ctx).to_string();
    assert_eq!(got, "<testing.unit (),testing.unit ()>");
}

#[test]
fn print_const_op() {
    let mut ctx = Context::new();
    register_dialect(&mut ctx);

    let i32_ty = IntegerType::get(&mut ctx, 32, true, 4);
    let const_value = ApInt::from(42);

    let const_op = ConstantOp::new_unlinked(&mut ctx, IntegerAttr::create(i32_ty, const_value));

    let got = const_op.disp(&ctx).to_string();
    assert_eq!(
        got,
        r#"op_0_0_res0 = "testing.const"() {"constant.value" = testing.int 0x2a: testing.int32<4,true>} : <() -> (testing.int32<4,true>)>"#
    );
}
