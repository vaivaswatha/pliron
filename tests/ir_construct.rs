use apint::ApInt;
use pliron::{
    common_traits::Verify,
    context::Context,
    debug_info::set_operation_result_name,
    dialects::{
        self,
        builtin::{
            attributes::IntegerAttr,
            op_interfaces::OneResultInterface,
            ops::{ConstantOp, FuncOp, ModuleOp},
            types::{FunctionType, IntegerType, Signedness},
        },
        llvm::ops::ReturnOp,
    },
    error::CompilerError,
    op::Op,
    with_context::AttachContext,
};

// Create a print a module "bar", with a function "foo"
// containing a single `return 0`.
#[test]
fn const_ret_in_mod() -> Result<(), CompilerError> {
    let ctx = &mut Context::new();
    dialects::builtin::register(ctx);
    dialects::llvm::register(ctx);

    let module = ModuleOp::new(ctx, "bar");
    // Our function is going to have type () -> ().
    let func_ty = FunctionType::get(ctx, vec![], vec![]);
    let func = FuncOp::new_unlinked(ctx, "foo", func_ty);
    module.add_operation(ctx, func.get_operation());
    let bb = func.get_entry_block(ctx);

    // Create a `const 0` op and add it to bb.
    let i64_ty = IntegerType::get(ctx, 64, Signedness::Signed);
    let zero_const = IntegerAttr::create(i64_ty, ApInt::from(0));
    let const_op = ConstantOp::new_unlinked(ctx, zero_const);
    const_op.get_operation().insert_at_front(bb, ctx);
    set_operation_result_name(ctx, const_op.get_operation(), 0, "c0".to_string());

    // Return the constant.
    let const_op_res = (&*const_op.get_result(&ctx)).into();
    let ret_op = ReturnOp::new_unlinked(ctx, const_op_res);
    ret_op.get_operation().insert_at_back(bb, ctx);

    print!("{}\n", module.with_ctx(ctx));
    module.verify(ctx)
}
