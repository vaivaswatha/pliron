mod common;

use std::sync::{LazyLock, Mutex};

use common::ReturnOp;
use expect_test::expect;
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
    decl_attr_interface, decl_type_interface,
    identifier::Identifier,
    impl_attr_interface, impl_canonical_syntax, impl_type_interface, impl_verify_succ,
    location::Location,
    op::{op_cast, Op, OpObj},
    operation::Operation,
    parsable::{Parsable, ParseResult, StateStream},
    printable::{self, Printable},
    r#type::{Type, TypeObj},
    result::{Error, ErrorKind, Result},
    utils::trait_cast::any_to_trait,
};
use pliron_derive::{
    def_attribute, def_op, def_type, derive_op_interface_impl, op_interface, op_interface_impl,
};

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
        *Operation::get_op(op, ctx).downcast_ref().unwrap()
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
            loc: _,
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
        *Operation::get_op(op, ctx).downcast_ref().unwrap()
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

decl_attr_interface! {
    TestAttrInterfaceX {
        fn verify(_op: &dyn Attribute, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            Ok(())
        }
    }
}

impl_attr_interface!(TestAttrInterfaceX for StringAttr {});
impl_attr_interface!(TestAttrInterfaceX for IntegerAttr {});

#[def_attribute("test.my_attr")]
#[derive(PartialEq, Clone, Debug)]
struct MyAttr {
    ty: Ptr<TypeObj>,
}
impl Verify for MyAttr {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl Printable for MyAttr {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "MyAttr")
    }
}
impl_attr_interface!(TypedAttrInterface for MyAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        self.ty
    }
});

static TEST_ATTR_VERIFIERS_OUTPUT: LazyLock<Mutex<String>> =
    LazyLock::new(|| Mutex::new("".into()));

#[def_attribute("test.verify_intr_attr")]
#[derive(PartialEq, Clone, Debug)]
struct VerifyIntrAttr {}
impl_verify_succ!(VerifyIntrAttr);
impl_attr_interface!(TestAttrInterface for VerifyIntrAttr {});
impl_attr_interface!(TestAttrInterface2 for VerifyIntrAttr {});

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

decl_attr_interface! {
    TestAttrInterface {
        fn verify(_op: &dyn Attribute, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            *TEST_ATTR_VERIFIERS_OUTPUT.lock().unwrap() += "TestAttrInterface verified\n";
            Ok(())
        }
    }
}

decl_attr_interface! {
    TestAttrInterface2: TestAttrInterface {
        fn verify(_op: &dyn Attribute, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            *TEST_ATTR_VERIFIERS_OUTPUT.lock().unwrap() += "TestAttrInterface2 verified\n";
            Ok(())
        }
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

decl_type_interface! {
    TestTypeInterfaceX {
        fn verify(_op: &dyn Type, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            Ok(())
        }
    }
}

impl_type_interface!(TestTypeInterfaceX for UnitType {});
impl_type_interface!(TestTypeInterfaceX for IntegerType {});

static TEST_TYPE_VERIFIERS_OUTPUT: LazyLock<Mutex<String>> =
    LazyLock::new(|| Mutex::new("".into()));

#[def_type("test.verify_intr_type")]
#[derive(PartialEq, Clone, Debug, Hash)]
struct VerifyIntrType {}
impl_verify_succ!(VerifyIntrType);
impl_type_interface!(TestTypeInterface for VerifyIntrType {});
impl_type_interface!(TestTypeInterface2 for VerifyIntrType {});

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

decl_type_interface! {
    TestTypeInterface {
        fn verify(_op: &dyn Type, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            *TEST_TYPE_VERIFIERS_OUTPUT.lock().unwrap() += "TestTypeInterface verified\n";
            Ok(())
        }
    }
}

decl_type_interface! {
    TestTypeInterface2: TestTypeInterface {
        fn verify(_op: &dyn Type, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            *TEST_TYPE_VERIFIERS_OUTPUT.lock().unwrap() += "TestTypeInterface2 verified\n";
            Ok(())
        }
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
