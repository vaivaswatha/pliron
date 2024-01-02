mod common;

use combine::{error::StdParseResult2, StreamOnce};
use pliron::{
    attribute::Attribute,
    common_traits::Verify,
    context::{Context, Ptr},
    declare_op,
    dialect::{Dialect, DialectName},
    dialects::{
        builtin::{
            attr_interfaces::TypedAttrInterface,
            attributes::StringAttr,
            op_interfaces::{OneResultInterface, OneResultVerifyErr},
        },
        llvm::ops::ReturnOp,
    },
    error::{Error, ErrorKind, Result},
    identifier::Identifier,
    impl_attr, impl_attr_interface, impl_op_interface,
    op::{Op, OpObj},
    operation::Operation,
    parsable::{Parsable, StateStream},
    printable::{self, Printable},
    r#type::TypeObj,
};

use crate::common::{const_ret_in_mod, setup_context_dialects};

declare_op!(ZeroResultOp, "zero_results", "test");

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

impl Verify for ZeroResultOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

impl Parsable for ZeroResultOp {
    type Arg = Vec<Identifier>;
    type Parsed = OpObj;
    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> StdParseResult2<Self::Parsed, <StateStream<'a> as StreamOnce>::Error> {
        todo!()
    }
}

impl ZeroResultOp {
    fn new(ctx: &mut Context) -> ZeroResultOp {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], 1);
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
            err
        })
        if err.is::<OneResultVerifyErr>()
    ))
}

pub trait TestOpInterface: Op {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

impl_op_interface!(TestOpInterface for ReturnOp {});
impl_op_interface!(TestOpInterface for pliron::dialects::builtin::ops::ModuleOp {});

pub trait TestAttrInterface: Attribute {
    fn verify(_op: &dyn Attribute, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

impl_op_interface!(TestAttrInterface for StringAttr {});
impl_op_interface!(TestAttrInterface for pliron::dialects::builtin::attributes::IntegerAttr {});

#[derive(PartialEq, Clone)]
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
impl_attr!(MyAttr, "my_attr", "test");
impl_attr_interface!(TypedAttrInterface for MyAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        self.ty
    }
});
