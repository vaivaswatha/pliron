mod common;

use std::sync::Mutex;

use expect_test::expect;
use pliron::{
    attribute::Attribute,
    builtin::{
        attr_interfaces::TypedAttrInterface,
        attributes::{IntegerAttr, StringAttr},
        op_interfaces::{OneResultInterface, OneResultVerifyErr},
        ops::ModuleOp,
    },
    common_traits::Verify,
    context::{Context, Ptr},
    decl_attr_interface, decl_op_interface,
    dialect::{Dialect, DialectName},
    error::{Error, ErrorKind, Result},
    identifier::Identifier,
    impl_attr_interface, impl_canonical_syntax, impl_op_interface, impl_verify_succ,
    location::Location,
    op::{op_cast, Op, OpObj},
    operation::Operation,
    parsable::{Parsable, ParseResult, StateStream},
    printable::{self, Printable},
    r#type::TypeObj,
    trait_cast::any_to_trait,
};
use pliron_derive::{def_attribute, def_op};
use pliron_llvm::ops::ReturnOp;

use crate::common::{const_ret_in_mod, setup_context_dialects};

#[def_op("test.zero_result")]
struct ZeroResultOp {}

// This is setup to fail.
impl_op_interface!(OneResultInterface for ZeroResultOp {});

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
    let mut dialect = Dialect::new(DialectName::new("test"));
    ZeroResultOp::register(ctx, &mut dialect, ZeroResultOp::parser_fn);

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
use pliron::Lazy;
static TEST_OP_VERIFIERS_OUTPUT: Lazy<Mutex<String>> = Lazy::new(|| Mutex::new("".into()));

decl_op_interface! {
    TestOpInterfaceX {
        fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            Ok(())
        }
    }
}

impl_op_interface!(TestOpInterfaceX for ReturnOp {});
impl_op_interface!(TestOpInterfaceX for ModuleOp {});

decl_op_interface! {
    TestOpInterface {
        fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            *TEST_OP_VERIFIERS_OUTPUT.lock().unwrap() += "TestOpInterface verified\n";
            Ok(())
        }
    }
}

decl_op_interface! {
    TestOpInterface2: TestOpInterface {
        fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            *TEST_OP_VERIFIERS_OUTPUT.lock().unwrap() += "TestOpInterface2 verified\n";"TestOpInterface2 verified\n";
            Ok(())
        }
    }
}

#[def_op("test.verify_intr_op")]
struct VerifyIntrOp {}
impl_canonical_syntax!(VerifyIntrOp);
impl_verify_succ!(VerifyIntrOp);
impl_op_interface!(TestOpInterface for VerifyIntrOp {});
impl_op_interface!(TestOpInterface2 for VerifyIntrOp {});
impl VerifyIntrOp {
    fn new(ctx: &mut Context) -> VerifyIntrOp {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], vec![], 1);
        *Operation::get_op(op, ctx).downcast_ref().unwrap()
    }
}

#[test]
fn test_op_intr_verify_order() -> Result<()> {
    let ctx = &mut setup_context_dialects();
    let mut dialect = Dialect::new(DialectName::new("test"));
    VerifyIntrOp::register(ctx, &mut dialect, VerifyIntrOp::parser_fn);

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

impl_attr_interface!(TestAttrInterface for StringAttr {});
impl_attr_interface!(TestAttrInterface for IntegerAttr {});

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

static TEST_ATTR_VERIFIERS_OUTPUT: Lazy<Mutex<String>> = Lazy::new(|| Mutex::new("".into()));

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
    let mut dialect = Dialect::new(DialectName::new("test"));
    VerifyIntrOp::register(ctx, &mut dialect, VerifyIntrOp::parser_fn);

    let vio = VerifyIntrAttr {};
    vio.verify_interfaces(ctx)?;

    expect![[r#"
        TestAttrInterface verified
        TestAttrInterface2 verified
    "#]]
    .assert_eq(&TEST_ATTR_VERIFIERS_OUTPUT.lock().unwrap());
    Ok(())
}
