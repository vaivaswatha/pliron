use apint::ApInt;
use expect_test::expect;
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

pub fn setup_context_dialects() -> Context {
    let mut ctx = Context::new();
    dialects::builtin::register(&mut ctx);
    dialects::llvm::register(&mut ctx);
    ctx
}

// Create a print a module "bar", with a function "foo"
// containing a single `return 0`.
pub fn const_ret_in_mod(
    ctx: &mut Context,
) -> Result<(ModuleOp, FuncOp, ConstantOp, ReturnOp), CompilerError> {
    let i64_ty = IntegerType::get(ctx, 64, Signedness::Signed);
    let module = ModuleOp::new(ctx, "bar");
    // Our function is going to have type () -> ().
    let func_ty = FunctionType::get(ctx, vec![], vec![i64_ty]);
    let func = FuncOp::new_unlinked(ctx, "foo", func_ty);
    module.add_operation(ctx, func.get_operation());
    let bb = func.get_entry_block(ctx);

    // Create a `const 0` op and add it to bb.
    let zero_const = IntegerAttr::create(i64_ty, ApInt::from(0));
    let const_op = ConstantOp::new_unlinked(ctx, zero_const);
    const_op.get_operation().insert_at_front(bb, ctx);
    set_operation_result_name(ctx, const_op.get_operation(), 0, "c0".to_string());

    // Return the constant.
    let ret_op = ReturnOp::new_unlinked(ctx, const_op.get_result(ctx));
    ret_op.get_operation().insert_at_back(bb, ctx);

    let printed = format!("{}", module.with_ctx(ctx));
    expect![[r#"
        builtin.module @bar {
          block_0_0():
            builtin.func @foo() -> (si64,) {
              entry():
                c0 = builtin.constant 0x0: si64
                llvm.return c0
            }
        }"#]]
    .assert_eq(&printed);

    module.get_operation().verify(ctx)?;

    Ok((module, func, const_op, ret_op))
}
