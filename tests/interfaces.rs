mod common;

use std::sync::{LazyLock, Mutex};

use common::ReturnOp;
use expect_test::expect;
use pliron::derive::{
    attr_interface, attr_interface_impl, def_attribute, def_op, def_type, derive_op_interface_impl,
    op_interface, op_interface_impl, type_interface, type_interface_impl,
};
use pliron::verify_err;
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
use pliron_derive::format_attribute;
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
        let op = Operation::new(ctx, Self::opid_static(), vec![], vec![], vec![], 1);
        *Operation::op(op, ctx).downcast_ref().unwrap()
    }
}

// A simple test to trigger an interface verification error.
#[test]
fn check_intrf_verfiy_errs() {
    let ctx = &mut setup_context_dialects();
    ZeroResultOp::register(ctx, ZeroResultOp::parser_fn);

    let zero_res_op = ZeroResultOp::new(ctx).operation();
    let (module_op, _, _, ret_op) = const_ret_in_mod(ctx).unwrap();
    zero_res_op.insert_before(ctx, ret_op.operation());

    assert!(matches!(
        module_op.operation().verify(ctx),
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
        let op = Operation::new(ctx, Self::opid_static(), vec![], vec![], vec![], 1);
        *Operation::op(op, ctx).downcast_ref().unwrap()
    }
}

#[test]
fn test_op_intr_verify_order() -> Result<()> {
    let ctx = &mut setup_context_dialects();
    VerifyIntrOp::register(ctx, VerifyIntrOp::parser_fn);

    let vio = VerifyIntrOp::new(ctx);

    vio.operation().deref(ctx).verify(ctx)?;

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
#[derive(PartialEq, Clone, Debug)]
struct MyAttr {
    ty: Ptr<TypeObj>,
}
impl_verify_succ!(MyAttr);

#[attr_interface_impl]
impl TypedAttrInterface for MyAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        self.ty
    }
}

static TEST_ATTR_VERIFIERS_OUTPUT: LazyLock<Mutex<String>> =
    LazyLock::new(|| Mutex::new("".into()));

#[def_attribute("test.verify_intr_attr")]
#[derive(PartialEq, Clone, Debug)]
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
    vio.verify_interfaces(ctx)?;

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
    vio.verify_interfaces(ctx)?;

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
        let op = Operation::new(ctx, Self::opid_static(), vec![], vec![], vec![], 1);
        *Operation::op(op, ctx).downcast_ref().unwrap()
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

    vio.operation().deref(ctx).verify(ctx)?;

    Ok(())
}

#[def_op("test.no_inbuilt_verify_op2")]
struct NoInbuiltVerifyOp2 {}
impl_canonical_syntax!(NoInbuiltVerifyOp2);
impl_verify_succ!(NoInbuiltVerifyOp2);
impl NoInbuiltVerifyOp2 {
    fn new(ctx: &mut Context) -> NoInbuiltVerifyOp2 {
        let op = Operation::new(ctx, Self::opid_static(), vec![], vec![], vec![], 1);
        *Operation::op(op, ctx).downcast_ref().unwrap()
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
        vio.operation().verify(ctx),
        Err(Error {
            kind: ErrorKind::VerificationFailed,
            err,
            ..
        })
        if err.is::<NoInbuiltVerifyOp2Error>()
    ));

    Ok(())
}
