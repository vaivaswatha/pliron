use apint::ApInt;
use expect_test::expect;
use pliron::{
    common_traits::Verify,
    debug_info::set_operation_result_name,
    dialects::builtin::{
        attributes::IntegerAttr, op_interfaces::OneResultInterface, ops::ConstantOp,
    },
    error::CompilerError,
    op::Op,
    operation::Operation,
    printable::Printable,
};

use crate::common::{const_ret_in_mod, setup_context_dialects};

mod common;

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

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar {
          block_0_0():
            builtin.func @foo() -> (si64) {
              entry():
                c0 = builtin.constant 0x0: si64
                c1 = builtin.constant 0x1: si64
                llvm.return c0
            }
        }"#]]
    .assert_eq(&printed);

    ret_op
        .get_operation()
        .deref_mut(ctx)
        .replace_operand(ctx, 0, const1_op.get_result(ctx));
    Operation::erase(const_op.get_operation(), ctx);

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar {
          block_0_0():
            builtin.func @foo() -> (si64) {
              entry():
                c1 = builtin.constant 0x1: si64
                llvm.return c1
            }
        }"#]]
    .assert_eq(&printed);

    module_op.get_operation().verify(ctx)?;

    Ok(())
}
