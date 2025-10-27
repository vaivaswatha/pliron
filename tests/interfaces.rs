mod common;

use std::sync::{LazyLock, Mutex};

use combine::Parser;
use combine::stream::position::SourcePosition;
use common::{ConstantOp, ReturnOp};
use expect_test::expect;
use pliron::attribute::verify_attr;
use pliron::builtin::attr_interfaces::{OutlinedAttr, PrintOnceAttr};
use pliron::derive::{
    attr_interface, attr_interface_impl, def_attribute, def_op, def_type, derive_op_interface_impl,
    op_interface, op_interface_impl, type_interface, type_interface_impl,
};
use pliron::location::{self, Located, Source};
use pliron::parsable::{self, state_stream_from_iterator};
use pliron::result::ExpectOk;
use pliron::r#type::verify_type;
use pliron::{
    attribute::Attribute,
    builtin::{
        attr_interfaces::TypedAttrInterface,
        attributes::{IntegerAttr, StringAttr},
        op_interfaces::{OneResultInterface, OneResultVerifyErr},
        ops::ModuleOp,
        types::{IntegerType, UnitType},
    },
    common_traits::Verify,
    context::{Context, Ptr},
    identifier::Identifier,
    impl_canonical_syntax, impl_verify_succ,
    location::Location,
    op::{Op, OpObj, op_cast},
    operation::Operation,
    parsable::{Parsable, ParseResult, StateStream},
    printable::{self, Printable},
    result::{Error, ErrorKind, Result},
    r#type::{Type, TypeObj},
    utils::trait_cast::any_to_trait,
};
use pliron::{input_error, verify_err};
use pliron_derive::{format_attribute, format_op};
use thiserror::Error;

use crate::common::{const_ret_in_mod, setup_context_dialects};

#[def_op("test.zero_result")]
struct ZeroResultOp {}

// This is setup to fail.
#[op_interface_impl]
impl OneResultInterface for ZeroResultOp {}

impl Printable for ZeroResultOp {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "zero_results",)
    }
}

impl_verify_succ!(ZeroResultOp);

impl Parsable for ZeroResultOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;
    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        unimplemented!()
    }
}

impl ZeroResultOp {
    fn new(ctx: &mut Context) -> ZeroResultOp {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], vec![], 1);
        Self { op }
    }
}

// A simple test to trigger an interface verification error.
#[test]
fn check_intrf_verfiy_errs() {
    let ctx = &mut setup_context_dialects();
    ZeroResultOp::register(ctx, ZeroResultOp::parser_fn);

    let zero_res_op = ZeroResultOp::new(ctx).get_operation();
    let (module_op, _, _, ret_op) = const_ret_in_mod(ctx).unwrap();
    zero_res_op.insert_before(ctx, ret_op.get_operation());

    assert!(matches!(
        module_op.get_operation().verify(ctx),
        Err(Error {
            kind: ErrorKind::VerificationFailed,
            err,
            ..
        })
        if err.is::<OneResultVerifyErr>()
    ))
}

static TEST_OP_VERIFIERS_OUTPUT: LazyLock<Mutex<String>> = LazyLock::new(|| Mutex::new("".into()));

#[op_interface]
trait TestOpInterfaceX {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

#[op_interface_impl]
impl TestOpInterfaceX for ReturnOp {}
#[op_interface_impl]
impl TestOpInterfaceX for ModuleOp {}

#[op_interface]
trait TestOpInterface {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        *TEST_OP_VERIFIERS_OUTPUT.lock().unwrap() += "TestOpInterface verified\n";
        Ok(())
    }
}

#[op_interface]
trait TestOpInterface2: TestOpInterface {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        *TEST_OP_VERIFIERS_OUTPUT.lock().unwrap() += "TestOpInterface2 verified\n";
        Ok(())
    }
}

#[def_op("test.verify_intr_op")]
#[derive_op_interface_impl(TestOpInterface, TestOpInterface2)]
struct VerifyIntrOp {}
impl_canonical_syntax!(VerifyIntrOp);
impl_verify_succ!(VerifyIntrOp);
impl VerifyIntrOp {
    fn new(ctx: &mut Context) -> VerifyIntrOp {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], vec![], 1);
        Self { op }
    }
}

#[test]
fn test_op_intr_verify_order() -> Result<()> {
    let ctx = &mut setup_context_dialects();
    VerifyIntrOp::register(ctx, VerifyIntrOp::parser_fn);

    let vio = VerifyIntrOp::new(ctx);

    vio.get_operation().deref(ctx).verify(ctx)?;

    expect![[r#"
        TestOpInterface verified
        TestOpInterface2 verified
    "#]]
    .assert_eq(&TEST_OP_VERIFIERS_OUTPUT.lock().unwrap());

    // Ad-hoc op interface conversions test.
    let x = op_cast::<dyn TestOpInterface>(&vio).unwrap();
    any_to_trait::<dyn TestOpInterface2>(x.as_any()).unwrap();

    Ok(())
}

#[attr_interface]
trait TestAttrInterfaceX {
    fn verify(_op: &dyn Attribute, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

#[attr_interface_impl]
impl TestAttrInterfaceX for StringAttr {}
#[attr_interface_impl]
impl TestAttrInterfaceX for IntegerAttr {}

#[def_attribute("test.my_attr")]
#[format_attribute("`<` $ty `>`")]
#[derive(PartialEq, Clone, Debug, Hash)]
struct MyAttr {
    ty: Ptr<TypeObj>,
}
impl_verify_succ!(MyAttr);

#[attr_interface_impl]
impl TypedAttrInterface for MyAttr {
    fn get_type(&self, _ctx: &Context) -> Ptr<TypeObj> {
        self.ty
    }
}

static TEST_ATTR_VERIFIERS_OUTPUT: LazyLock<Mutex<String>> =
    LazyLock::new(|| Mutex::new("".into()));

#[def_attribute("test.verify_intr_attr")]
#[derive(PartialEq, Clone, Debug, Hash)]
struct VerifyIntrAttr {}
impl_verify_succ!(VerifyIntrAttr);

#[attr_interface_impl]
impl TestAttrInterface for VerifyIntrAttr {}
#[attr_interface_impl]
impl TestAttrInterface2 for VerifyIntrAttr {}

impl Printable for VerifyIntrAttr {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "VerifyIntAttr")
    }
}

#[attr_interface]
trait TestAttrInterface {
    fn verify(_op: &dyn Attribute, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        *TEST_ATTR_VERIFIERS_OUTPUT.lock().unwrap() += "TestAttrInterface verified\n";
        Ok(())
    }
}

#[attr_interface]
trait TestAttrInterface2: TestAttrInterface {
    fn verify(_op: &dyn Attribute, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        *TEST_ATTR_VERIFIERS_OUTPUT.lock().unwrap() += "TestAttrInterface2 verified\n";
        Ok(())
    }
}

#[test]
fn test_attr_intr_verify_order() -> Result<()> {
    let ctx = &mut setup_context_dialects();
    VerifyIntrOp::register(ctx, VerifyIntrOp::parser_fn);

    let vio = VerifyIntrAttr {};
    verify_attr(&vio, ctx)?;

    expect![[r#"
        TestAttrInterface verified
        TestAttrInterface2 verified
    "#]]
    .assert_eq(&TEST_ATTR_VERIFIERS_OUTPUT.lock().unwrap());
    Ok(())
}

#[type_interface]
trait TestTypeInterfaceX {
    fn verify(_op: &dyn Type, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

#[type_interface_impl]
impl TestTypeInterfaceX for UnitType {}
#[type_interface_impl]
impl TestTypeInterfaceX for IntegerType {}

static TEST_TYPE_VERIFIERS_OUTPUT: LazyLock<Mutex<String>> =
    LazyLock::new(|| Mutex::new("".into()));

#[def_type("test.verify_intr_type")]
#[derive(PartialEq, Clone, Debug, Hash)]
struct VerifyIntrType {}
impl_verify_succ!(VerifyIntrType);
#[type_interface_impl]
impl TestTypeInterface for VerifyIntrType {}
#[type_interface_impl]
impl TestTypeInterface2 for VerifyIntrType {}

impl Printable for VerifyIntrType {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "VerifyIntType")
    }
}

#[type_interface]
trait TestTypeInterface {
    fn verify(_op: &dyn Type, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        *TEST_TYPE_VERIFIERS_OUTPUT.lock().unwrap() += "TestTypeInterface verified\n";
        Ok(())
    }
}

#[type_interface]
trait TestTypeInterface2: TestTypeInterface {
    fn verify(_op: &dyn Type, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        *TEST_TYPE_VERIFIERS_OUTPUT.lock().unwrap() += "TestTypeInterface2 verified\n";
        Ok(())
    }
}

#[test]
fn test_type_intr_verify_order() -> Result<()> {
    let ctx = &mut setup_context_dialects();
    VerifyIntrOp::register(ctx, VerifyIntrOp::parser_fn);

    let vio = VerifyIntrType {};
    verify_type(&vio, ctx)?;

    expect![[r#"
        TestTypeInterface verified
        TestTypeInterface2 verified
    "#]]
    .assert_eq(&TEST_TYPE_VERIFIERS_OUTPUT.lock().unwrap());
    Ok(())
}

#[op_interface]
trait TestNoInbuiltVerifyInterface {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized;
}

#[def_op("test.no_inbuilt_verify_op")]
struct NoInbuiltVerifyOp {}
impl_canonical_syntax!(NoInbuiltVerifyOp);
impl_verify_succ!(NoInbuiltVerifyOp);
impl NoInbuiltVerifyOp {
    fn new(ctx: &mut Context) -> NoInbuiltVerifyOp {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], vec![], 1);
        Self { op }
    }
}

#[op_interface_impl]
impl TestNoInbuiltVerifyInterface for NoInbuiltVerifyOp {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

#[test]
fn test_no_inbuilt_verify() -> Result<()> {
    let ctx = &mut setup_context_dialects();
    NoInbuiltVerifyOp::register(ctx, NoInbuiltVerifyOp::parser_fn);

    let vio = NoInbuiltVerifyOp::new(ctx);

    vio.get_operation().deref(ctx).verify(ctx)?;

    Ok(())
}

#[def_op("test.no_inbuilt_verify_op2")]
struct NoInbuiltVerifyOp2 {}
impl_canonical_syntax!(NoInbuiltVerifyOp2);
impl_verify_succ!(NoInbuiltVerifyOp2);
impl NoInbuiltVerifyOp2 {
    fn new(ctx: &mut Context) -> NoInbuiltVerifyOp2 {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], vec![], 1);
        Self { op }
    }
}

#[derive(Error, Debug)]
#[error("No inbuilt verify op2 error")]
pub struct NoInbuiltVerifyOp2Error;

#[op_interface_impl]
impl TestNoInbuiltVerifyInterface for NoInbuiltVerifyOp2 {
    fn verify(op: &dyn Op, ctx: &Context) -> Result<()> {
        verify_err!(op.loc(ctx), NoInbuiltVerifyOp2Error)
    }
}

#[test]
fn test_no_inbuilt_verify2() -> Result<()> {
    let ctx = &mut setup_context_dialects();
    NoInbuiltVerifyOp2::register(ctx, NoInbuiltVerifyOp2::parser_fn);

    let vio = NoInbuiltVerifyOp2::new(ctx);

    assert!(matches!(
        vio.get_operation().verify(ctx),
        Err(Error {
            kind: ErrorKind::VerificationFailed,
            err,
            ..
        })
        if err.is::<NoInbuiltVerifyOp2Error>()
    ));

    Ok(())
}

#[def_attribute("test.outline_test_attr")]
#[format_attribute("`<` $ty `>`")]
#[derive(PartialEq, Clone, Debug, Hash)]
pub struct OutlineTestAttr {
    pub ty: Ptr<TypeObj>,
}

impl_verify_succ!(OutlineTestAttr);

#[attr_interface_impl]
impl OutlinedAttr for OutlineTestAttr {}

#[test]
fn test_outline_attr() -> Result<()> {
    let ctx = &mut setup_context_dialects();
    OutlineTestAttr::register_attr_in_dialect(ctx, OutlineTestAttr::parser_fn);
    let attr = OutlineTestAttr {
        ty: IntegerType::get(ctx, 32, pliron::builtin::types::Signedness::Signed).into(),
    };

    let op = ConstantOp::new(ctx, 42);
    op.get_operation()
        .deref_mut(ctx)
        .attributes
        .0
        .insert("test_attr".try_into().unwrap(), Box::new(attr));

    // Print the op
    let printed = op.get_operation().deref(ctx).disp(ctx).to_string();

    expect![[r#"
        op1v1_res0 = test.constant builtin.integer <42: si64> !0

        outlined_attributes:
        !0 = [test_attr = test.outline_test_attr <builtin.integer si32>]
    "#]]
    .assert_eq(&printed);

    Ok(())
}

#[def_attribute("test.outline_print_once_test_attr")]
#[format_attribute("`<` $ty `>`")]
#[derive(PartialEq, Clone, Debug, Hash)]
pub struct OulinePrintOnceTestAttr {
    pub ty: Ptr<TypeObj>,
}

impl_verify_succ!(OulinePrintOnceTestAttr);

#[attr_interface_impl]
impl OutlinedAttr for OulinePrintOnceTestAttr {}
#[attr_interface_impl]
impl PrintOnceAttr for OulinePrintOnceTestAttr {}

#[test]
fn test_outline_printonce_attr() -> Result<()> {
    let ctx = &mut setup_context_dialects();
    OutlineTestAttr::register_attr_in_dialect(ctx, OutlineTestAttr::parser_fn);
    OulinePrintOnceTestAttr::register_attr_in_dialect(ctx, OulinePrintOnceTestAttr::parser_fn);

    let attr = OulinePrintOnceTestAttr {
        ty: IntegerType::get(ctx, 32, pliron::builtin::types::Signedness::Signed).into(),
    };

    let src = Source::new_from_file(ctx, "/tmp/test.pliron".into());

    let pos1 = SourcePosition::default();
    let loc1 = Location::SrcPos { src, pos: pos1 };

    let op42 = ConstantOp::new(ctx, 42);
    op42.get_operation().deref_mut(ctx).set_loc(loc1);
    let op44 = ConstantOp::new(ctx, 44);
    op42.get_operation().deref_mut(ctx).attributes.0.insert(
        "test_print_once_attr".try_into().unwrap(),
        Box::new(attr.clone()),
    );
    op44.get_operation()
        .deref_mut(ctx)
        .attributes
        .0
        .insert("test_print_once_attr".try_into().unwrap(), Box::new(attr));

    // Put them both in a function.
    let (module_op, _, _, ret_op) = const_ret_in_mod(ctx).unwrap();
    op42.get_operation()
        .insert_before(ctx, ret_op.get_operation());
    op44.get_operation()
        .insert_before(ctx, ret_op.get_operation());

    // Print the op
    let printed = module_op.get_operation().deref(ctx).disp(ctx).to_string();

    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                c0_op5v1_res0 = test.constant builtin.integer <0: si64>;
                op1v1_res0 = test.constant builtin.integer <42: si64> !0;
                op2v1_res0 = test.constant builtin.integer <44: si64> !1;
                test.return c0_op5v1_res0
            }
        }

        outlined_attributes:
        !0 = @["/tmp/test.pliron": line: 1, column: 1], [test_print_once_attr = !2]
        !1 = [test_print_once_attr = !2]
        !2 = test.outline_print_once_test_attr <builtin.integer si32>
    "#]]
    .assert_eq(&printed);

    // Try parsing the just printed output.

    let parsed_op = {
        let mut state_stream = state_stream_from_iterator(
            printed.chars(),
            parsable::State::new(ctx, location::Source::InMemory),
        );
        Operation::top_level_parser()
            .parse_stream(&mut state_stream)
            .into_result()
            .map_err(|err| {
                let err = err.into_inner();
                let pos = err.error.position;
                input_error!(Location::SrcPos { src, pos }, err.error)
            })
    };

    let parsed_op = parsed_op.expect_ok(ctx).0;

    parsed_op.verify(ctx)?;
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1_block4v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1_block3v1():
                c0_op5v1_res0_op9v1_res0 = test.constant builtin.integer <0: si64> !0;
                op1v1_res0_op10v1_res0 = test.constant builtin.integer <42: si64> !1;
                op2v1_res0_op11v1_res0 = test.constant builtin.integer <44: si64> !2;
                test.return c0_op5v1_res0_op9v1_res0 !3
            } !4
        } !5

        outlined_attributes:
        !0 = @[<in-memory>: line: 7, column: 9], []
        !1 = @["/tmp/test.pliron": line: 1, column: 1], [test_print_once_attr = !6]
        !2 = @[<in-memory>: line: 9, column: 9], [test_print_once_attr = !6]
        !3 = @[<in-memory>: line: 10, column: 9], []
        !4 = @[<in-memory>: line: 4, column: 5], []
        !5 = @[<in-memory>: line: 1, column: 1], []
        !6 = test.outline_print_once_test_attr <builtin.integer si32>
    "#]]
    .assert_eq(&parsed_op.disp(ctx).to_string());

    Ok(())
}

#[def_op("test.canonical_op")]
#[format_op]
pub struct CanonicalOp;
impl_verify_succ!(CanonicalOp);

impl CanonicalOp {
    pub fn new(ctx: &mut Context) -> CanonicalOp {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], vec![], 0);
        Self { op }
    }
}

#[test]
fn test_outline_attr_canonical_op() -> Result<()> {
    let ctx = &mut setup_context_dialects();

    CanonicalOp::register(ctx, CanonicalOp::parser_fn);
    OutlineTestAttr::register_attr_in_dialect(ctx, OutlineTestAttr::parser_fn);
    let attr = OutlineTestAttr {
        ty: IntegerType::get(ctx, 32, pliron::builtin::types::Signedness::Signed).into(),
    };

    let op = CanonicalOp::new(ctx);
    op.get_operation()
        .deref_mut(ctx)
        .attributes
        .0
        .insert("test_attr".try_into().unwrap(), Box::new(attr));

    // Print the op
    let printed = op.get_operation().deref(ctx).disp(ctx).to_string();

    expect![[r#"
        test.canonical_op () [] []: <() -> ()> !0

        outlined_attributes:
        !0 = [test_attr = test.outline_test_attr <builtin.integer si32>]
    "#]]
    .assert_eq(&printed);

    Ok(())
}
