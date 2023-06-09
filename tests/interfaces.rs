mod common;

use pliron::{
    attribute::Attribute,
    common_traits::{DisplayWithContext, Verify},
    context::{Context, Ptr},
    declare_op,
    dialect::{Dialect, DialectName},
    dialects::{
        builtin::{
            attr_interfaces::TypedAttrInterface, attributes::StringAttr,
            op_interfaces::OneResultInterface,
        },
        llvm::ops::ReturnOp,
    },
    error::CompilerError,
    impl_attr, impl_attr_interface, impl_op_interface,
    op::Op,
    operation::Operation,
    r#type::TypeObj,
};

use crate::common::{const_ret_in_mod, setup_context_dialects};

declare_op!(ZeroResultOp, "zero_results", "test");

impl_op_interface!(OneResultInterface for ZeroResultOp {});

impl DisplayWithContext for ZeroResultOp {
    fn fmt(&self, _ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "zero_results",)
    }
}

impl Verify for ZeroResultOp {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        Ok(())
    }
}

impl ZeroResultOp {
    fn new(ctx: &mut Context) -> ZeroResultOp {
        *Operation::new(ctx, Self::get_opid_static(), vec![], vec![], 1)
            .deref(ctx)
            .get_op(ctx)
            .downcast_ref()
            .unwrap()
    }
}

// A simple test to trigger an interface verification error.
#[test]
fn check_intrf_verfiy_errs() {
    let ctx = &mut setup_context_dialects();
    let mut dialect = Dialect::new(DialectName::new("test"));
    ZeroResultOp::register(ctx, &mut dialect);

    let zero_res_op = ZeroResultOp::new(ctx).get_operation();
    let (module_op, _, _, ret_op) = const_ret_in_mod(ctx).unwrap();
    zero_res_op.insert_before(ctx, ret_op.get_operation());

    assert!(matches!(
        module_op.get_operation().verify(ctx),
        Err(CompilerError::VerificationError { msg }) 
        if msg == "Expected exactly one result on operation test.zero_results"));
}

pub trait TestOpInterface: Op {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<(), CompilerError>
    where
        Self: Sized,
    {
        Ok(())
    }
}

impl_op_interface!(TestOpInterface for ReturnOp {});
impl_op_interface!(TestOpInterface for pliron::dialects::builtin::ops::ModuleOp {});

pub trait TestAttrInterface: Attribute {
    fn verify(_op: &dyn Attribute, _ctx: &Context) -> Result<(), CompilerError>
    where
        Self: Sized,
    {
        Ok(())
    }
}

impl_op_interface!(TestAttrInterface for StringAttr {});
impl_op_interface!(TestAttrInterface for pliron::dialects::builtin::attributes::IntegerAttr {});

#[derive(PartialEq)]
struct MyAttr {
    ty: Ptr<TypeObj>,
}
impl Verify for MyAttr {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        Ok(())
    }
}
impl DisplayWithContext for MyAttr {
    fn fmt(&self, _ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "MyAttr")
    }
}
impl_attr!(MyAttr, "my_attr", "test");
impl_attr_interface!(TypedAttrInterface for MyAttr {
    fn get_type(&self) -> Ptr<TypeObj> {
        self.ty
    }
});
