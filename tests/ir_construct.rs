use apint::ApInt;
use pliron::{
    common_traits::{DisplayWithContext, Verify},
    context::Context,
    debug_info::set_operation_result_name,
    declare_op,
    dialect::{Dialect, DialectName},
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
    impl_op_interface,
    op::Op,
    operation::Operation,
    with_context::AttachContext,
};

fn setup_context_dialects() -> Context {
    let mut ctx = Context::new();
    dialects::builtin::register(&mut ctx);
    dialects::llvm::register(&mut ctx);
    ctx
}

// Create a print a module "bar", with a function "foo"
// containing a single `return 0`.
fn const_ret_in_mod(
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

    println!("{}", module.with_ctx(ctx));
    module.verify(ctx)?;

    Ok((module, func, const_op, ret_op))
}

// Test erasing the entire top module.
#[test]
fn construct_and_erase() -> Result<(), CompilerError> {
    let ctx = &mut setup_context_dialects();
    let module_op = const_ret_in_mod(ctx)?.0.get_operation();
    Operation::erase(module_op, ctx);
    assert!(ctx.operations.is_empty() && ctx.basic_blocks.is_empty() && ctx.regions.is_empty());
    Ok(())
}

// Ensure that erasing an op with uses panics.
#[test]
#[should_panic(expected = "Operation with use(s) being erased")]
fn removed_used_op() {
    let ctx = &mut setup_context_dialects();

    // const_ret_in_mod builds a module with a function.
    let (_, _, const_op, _) = const_ret_in_mod(ctx).unwrap();

    // const_op is used in the return. Erasing it must panic.
    Operation::erase(const_op.get_operation(), ctx);
}

// Testing replacing all uses of c0 with c1.
#[test]
fn replace_c0_with_c1() -> Result<(), CompilerError> {
    let ctx = &mut setup_context_dialects();

    // const_ret_in_mod builds a module with a function.
    let (module_op, _, const_op, _) = const_ret_in_mod(ctx).unwrap();

    // Insert a new constant.
    let one_const = IntegerAttr::create(const_op.get_type(ctx), ApInt::from(1));
    let const1_op = ConstantOp::new_unlinked(ctx, one_const);
    const1_op
        .get_operation()
        .insert_after(ctx, const_op.get_operation());
    set_operation_result_name(ctx, const1_op.get_operation(), 0, "c1".to_string());
    let const0_val = const_op.get_result(ctx);
    const0_val.replace_some_uses_with(ctx, |_, _| true, &const1_op.get_result(ctx));

    Operation::erase(const_op.get_operation(), ctx);

    module_op.get_operation().verify(ctx)?;

    Ok(())
}

// Replace ret_op's first operand (which is c0) with c1.
// Erase c0. Verify.
#[test]
fn replace_c0_with_c1_operand() -> Result<(), CompilerError> {
    let ctx = &mut setup_context_dialects();

    // const_ret_in_mod builds a module with a function.
    let (module_op, _, const_op, ret_op) = const_ret_in_mod(ctx).unwrap();

    // Insert a new constant.
    let one_const = IntegerAttr::create(const_op.get_type(ctx), ApInt::from(1));
    let const1_op = ConstantOp::new_unlinked(ctx, one_const);
    const1_op
        .get_operation()
        .insert_after(ctx, const_op.get_operation());
    set_operation_result_name(ctx, const1_op.get_operation(), 0, "c1".to_string());

    ret_op
        .get_operation()
        .deref_mut(ctx)
        .replace_operand(ctx, 0, const1_op.get_result(ctx));
    Operation::erase(const_op.get_operation(), ctx);

    module_op.get_operation().verify(ctx)?;

    Ok(())
}

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
