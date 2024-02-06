use apint::ApInt;
use expect_test::{expect, Expect};
use pliron::{
    common_traits::Verify,
    debug_info::set_operation_result_name,
    dialects::builtin::{
        attributes::IntegerAttr, op_interfaces::OneResultInterface, ops::ConstantOp,
    },
    error::Result,
    location,
    op::Op,
    operation::Operation,
    parsable::{self, spaced, state_stream_from_iterator, Parsable},
    printable::Printable,
    r#type::TypePtr,
};

use crate::common::{const_ret_in_mod, setup_context_dialects};
use combine::parser::Parser;

mod common;

// Test erasing the entire top module.
#[test]
fn construct_and_erase() -> Result<()> {
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
fn replace_c0_with_c1() -> Result<()> {
    let ctx = &mut setup_context_dialects();

    // const_ret_in_mod builds a module with a function.
    let (module_op, _, const_op, _) = const_ret_in_mod(ctx).unwrap();

    // Insert a new constant.
    let one_const = IntegerAttr::create(
        TypePtr::new(const_op.get_type(ctx), ctx).expect("Expected const_op to have integer type"),
        ApInt::from(1),
    );
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
fn replace_c0_with_c1_operand() -> Result<()> {
    let ctx = &mut setup_context_dialects();

    // const_ret_in_mod builds a module with a function.
    let (module_op, _, const_op, ret_op) = const_ret_in_mod(ctx).unwrap();

    // Insert a new constant.
    let one_const = IntegerAttr::create(
        TypePtr::new(const_op.get_type(ctx), ctx).unwrap(),
        ApInt::from(1),
    );
    let const1_op = ConstantOp::new_unlinked(ctx, one_const);
    const1_op
        .get_operation()
        .insert_after(ctx, const_op.get_operation());
    set_operation_result_name(ctx, const1_op.get_operation(), 0, "c1".to_string());

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar {
          ^block_0_0():
            builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
              ^entry_block_1_0():
                c0_op_2_0_res0 = builtin.constant builtin.integer <0x0: builtin.int<si64>>;
                c1_op_4_0_res0 = builtin.constant builtin.integer <0x1: builtin.int<si64>>;
                llvm.return c0_op_2_0_res0
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
          ^block_0_0():
            builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
              ^entry_block_1_0():
                c1_op_4_0_res0 = builtin.constant builtin.integer <0x1: builtin.int<si64>>;
                llvm.return c1_op_4_0_res0
            }
        }"#]]
    .assert_eq(&printed);

    module_op.get_operation().verify(ctx)?;

    Ok(())
}

#[test]
/// A test to just print a constructed IR to stdout.
fn print_simple() -> Result<()> {
    let ctx = &mut setup_context_dialects();
    let module_op = const_ret_in_mod(ctx)?.0.get_operation();
    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar {
          ^block_0_0():
            builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
              ^entry_block_1_0():
                c0_op_2_0_res0 = builtin.constant builtin.integer <0x0: builtin.int<si64>>;
                llvm.return c0_op_2_0_res0
            }
        }"#]]
    .assert_eq(&printed);
    println!("{}", printed);
    Ok(())
}

#[test]
fn parse_simple() -> Result<()> {
    let input = r#"
        builtin.module @bar {
        ^block_0_0():
            builtin.func @foo: builtin.function <() -> (builtin.int <si64>)> {
            ^entry_block_1_0():
                c0_op_2_0_res0 = builtin.constant builtin.integer <0x0: builtin.int <si64>>;
                llvm.return c0_op_2_0_res0
            ^exit(a : builtin.int <si32>):
            }
        }"#;

    let ctx = &mut setup_context_dialects();
    let op = {
        let state_stream = state_stream_from_iterator(
            input.chars(),
            parsable::State::new(ctx, location::Source::InMemory),
        );
        spaced(Operation::parser(())).parse(state_stream).unwrap().0
    };
    println!("{}", op.disp(ctx));
    Ok(())
}

fn expect_parse_error(input: &str, expected_err: Expect) {
    let ctx = &mut setup_context_dialects();
    let state_stream = state_stream_from_iterator(
        input.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let actual_err = spaced(Operation::parser(()))
        .parse(state_stream)
        .err()
        .unwrap();

    expected_err.assert_eq(&actual_err.to_string());
}

#[test]
fn parse_err_multiple_def() {
    let input_multiple_ssa_defs = r#"
        builtin.module @bar {
        ^block_0_0():
            builtin.func @foo: builtin.function <() -> (builtin.int <si64>)> {
            ^entry_block_1_0():
                c0_op_2_0_res0 = builtin.constant builtin.integer <0x0: builtin.int <si64>>;
                c0_op_2_0_res0 = builtin.constant builtin.integer <0x0: builtin.int <si64>>;
                llvm.return c0_op_2_0_res0
            ^exit():
            }
        }"#;

    let expected_err = expect![[r#"
        Parse error at line: 7, column: 17
        Identifier c0_op_2_0_res0 defined more than once in the scope
    "#]];
    expect_parse_error(input_multiple_ssa_defs, expected_err);

    let input_multiple_label_defs = r#"
        builtin.module @bar {
        ^block_0_0():
            builtin.func @foo: builtin.function <() -> (builtin.int <si64>)> {
            ^entry_block_1_0():
                c0_op_2_0_res0 = builtin.constant builtin.integer <0x0: builtin.int <si64>>;
                llvm.return c0_op_2_0_res0
            ^entry_block_1_0():
            }
        }"#;

    let expected_err = expect![[r#"
        Parse error at line: 8, column: 13
        Identifier entry_block_1_0 defined more than once in the scope
    "#]];
    expect_parse_error(input_multiple_label_defs, expected_err);
}

#[test]
fn parse_err_unresolved_def() {
    let input_multiple_defs = r#"
        builtin.module @bar {
        ^block_0_0():
            builtin.func @foo: builtin.function <() -> (builtin.int <si64>)> {
            ^entry_block_1_0():
                llvm.return c0_op_2_0_res0
            }
        }"#;

    let expected_err = expect![[r#"
        Parse error at line: 4, column: 78
        Identifier c0_op_2_0_res0 was not resolved to any definition in the scope
    "#]];
    expect_parse_error(input_multiple_defs, expected_err);
}

#[test]
fn parse_err_block_label_colon() {
    let input_label_colon_missing = r#"
        builtin.module @bar {
        ^block_0_0():
            builtin.func @foo: builtin.function <() -> (builtin.int <si64>)> {
            ^entry_block_1_0():
                c0_op_2_0_res0 = builtin.constant builtin.integer <0x0: builtin.int <si64>>;
                llvm.return c0_op_2_0_res0
            ^exit()
            }
        }"#;

    let expected_err = expect![[r#"
        Parse error at line: 9, column: 13
        Unexpected `}`
        Expected whitespace or `:`
    "#]];

    expect_parse_error(input_label_colon_missing, expected_err);
}

#[test]
fn parse_err_block_args() {
    let input_label_colon_missing = r#"
        builtin.module @bar {
        ^block_0_0(a : builtin.int <si32>, b):
        }"#;

    let expected_err = expect![[r#"
        Parse error at line: 3, column: 45
        Unexpected `)`
        Expected whitespaces or `:`
    "#]];

    expect_parse_error(input_label_colon_missing, expected_err);
}
