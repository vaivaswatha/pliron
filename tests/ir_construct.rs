use apint::ApInt;
use pliron::{
    common_traits::Verify,
    context::Context,
    debug_info::set_operation_result_name,
    dialects::{
        self,
        builtin::{
            attributes::IntegerAttr,
            op_interfaces::{OneResultInterface, SingleBlockRegionInterface},
            ops::{ConstantOp, FuncOp, ModuleOp},
            types::{FunctionType, IntegerType, Signedness},
        },
        llvm::ops::ReturnOp,
    },
    error::CompilerError,
    linked_list::ContainsLinkedList,
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
fn const_ret_in_mod(ctx: &mut Context) -> Result<ModuleOp, CompilerError> {
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

    Ok(module)
}

#[test]
fn construct_and_erase() -> Result<(), CompilerError> {
    let ctx = &mut setup_context_dialects();
    let module_op = const_ret_in_mod(ctx)?.get_operation();
    Operation::erase(module_op, ctx);
    assert!(ctx.operations.is_empty() && ctx.basic_blocks.is_empty() && ctx.regions.is_empty());
    Ok(())
}

#[test]
#[should_panic(expected = "Operation with use(s) being erased")]
fn removed_used_op() {
    let ctx = &mut setup_context_dialects();

    // const_ret_in_mod builds a module with a function.
    let func_op = const_ret_in_mod(ctx)
        .unwrap()
        .get_body(ctx, 0)
        .deref(ctx)
        .get_head()
        .unwrap()
        .deref(ctx)
        .get_op(ctx);
    let func_op = func_op.downcast_ref::<FuncOp>().unwrap();

    // Search for the const_op in the function.
    let const_op = func_op
        .op_iter(ctx)
        .find(|op| op.deref(ctx).get_op(ctx).is::<ConstantOp>())
        .expect("Expected to find a constant op");

    // const_op is used in the return. Erasing it must panic.
    Operation::erase(const_op, ctx);
}
#[test]
fn replace_c0_with_c1() -> Result<(), CompilerError> {
    let ctx = &mut setup_context_dialects();
    let module = const_ret_in_mod(ctx).unwrap();

    // const_ret_in_mod builds a module with a function.
    let func_op = module
        .get_body(ctx, 0)
        .deref(ctx)
        .get_head()
        .unwrap()
        .deref(ctx)
        .get_op(ctx);
    let func_op = func_op.downcast_ref::<FuncOp>().unwrap();

    // Search for the const_op in the function.
    let const0_op_ptr = func_op
        .op_iter(ctx)
        .find(|op| op.deref(ctx).get_op(ctx).is::<ConstantOp>())
        .expect("Expected to find a constant op");
    let const0_op = *const0_op_ptr
        .deref(ctx)
        .get_op(ctx)
        .downcast_ref::<ConstantOp>()
        .unwrap();

    // Insert a new constant.
    let one_const = IntegerAttr::create(const0_op.get_type(ctx), ApInt::from(1));
    let const1_op = ConstantOp::new_unlinked(ctx, one_const);
    const1_op.get_operation().insert_after(ctx, const0_op_ptr);
    set_operation_result_name(ctx, const1_op.get_operation(), 0, "c1".to_string());
    let const0_val = const0_op.get_result(ctx);
    const0_val.replace_some_uses_with(ctx, |_, _| true, &const1_op.get_result(ctx));

    Operation::erase(const0_op_ptr, ctx);

    println!("{}", module.with_ctx(ctx));
    module.verify(ctx)?;

    Ok(())
}
