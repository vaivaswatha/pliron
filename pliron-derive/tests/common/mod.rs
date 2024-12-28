use pliron::{
    builtin::{self, op_interfaces::IsTerminatorInterface},
    context::Context,
    dialect::{Dialect, DialectName},
    impl_verify_succ,
    op::Op,
    parsable::Parsable,
};
use pliron_derive::{def_op, derive_op_interface_impl, format_op};

#[def_op("test.return")]
#[format_op("$0")]
#[derive_op_interface_impl(IsTerminatorInterface)]
pub struct ReturnOp;
impl_verify_succ!(ReturnOp);

pub fn setup_context_dialects() -> Context {
    let mut ctx = Context::new();
    builtin::register(&mut ctx);

    // Create a test dialect for test ops/attributes and types.
    let test_dialect = Dialect::new(DialectName::new("test"));
    test_dialect.register(&mut ctx);

    // Register test ops.
    ReturnOp::register(&mut ctx, ReturnOp::parser_fn);

    ctx
}
