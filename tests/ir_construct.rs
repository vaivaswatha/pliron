use common::{ConstantOp, ReturnOp};
use expect_test::{expect, Expect};
use pliron::{
    basic_block::BasicBlock,
    builtin::{
        op_interfaces::OneResultInterface,
        types::{IntegerType, Signedness},
    },
    common_traits::Verify,
    context::Context,
    debug_info::set_operation_result_name,
    graph::walkers::{
        self,
        interruptible::{self, walk_advance, walk_break},
        IRNode, WALKCONFIG_POSTORDER_FORWARD, WALKCONFIG_POSTORDER_REVERSE,
        WALKCONFIG_PREORDER_FORWARD,
    },
    impl_canonical_syntax, impl_verify_succ,
    irfmt::parsers::spaced,
    location,
    op::Op,
    operation::Operation,
    parsable::{self, state_stream_from_iterator, Parsable},
    printable::Printable,
    result::Result,
};
use pliron_derive::def_op;

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

    let const1_op = ConstantOp::new(ctx, 1);
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

    let const1_op = ConstantOp::new(ctx, 1);
    const1_op
        .get_operation()
        .insert_after(ctx, const_op.get_operation());
    set_operation_result_name(ctx, const1_op.get_operation(), 0, "c1".to_string());

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar {
          ^block_1v1():
            builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
              ^entry_block_2v1():
                c0_op_3v1_res0 = test.constant builtin.integer <0x0: builtin.int<si64>>;
                c1_op_5v1_res0 = test.constant builtin.integer <0x1: builtin.int<si64>>;
                test.return c0_op_3v1_res0
            }
        }"#]]
    .assert_eq(&printed);

    Operation::replace_operand(ret_op.get_operation(), ctx, 0, const1_op.get_result(ctx));
    Operation::erase(const_op.get_operation(), ctx);

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar {
          ^block_1v1():
            builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
              ^entry_block_2v1():
                c1_op_5v1_res0 = test.constant builtin.integer <0x1: builtin.int<si64>>;
                test.return c1_op_5v1_res0
            }
        }"#]]
    .assert_eq(&printed);

    module_op.get_operation().verify(ctx)?;

    Ok(())
}

#[def_op("test.dual_def")]
struct DualDefOp {}
impl_verify_succ!(DualDefOp);
impl_canonical_syntax!(DualDefOp);

/// If an Op has multiple results, or a block multiple args,
/// replacing all uses of one with the other should work.
/// (since our RefCell is at the Op or block level, we shouldn't
/// end up with a multiple borrow panic).
#[test]
fn test_replace_within_same_def_site() {
    let ctx = &mut setup_context_dialects();
    DualDefOp::register(ctx, DualDefOp::parser_fn);

    let u64_ty = IntegerType::get(ctx, 64, Signedness::Signed).into();

    let dual_def_op = Operation::new(
        ctx,
        DualDefOp::get_opid_static(),
        vec![u64_ty, u64_ty],
        vec![],
        vec![],
        0,
    );
    let (res1, res2) = (
        dual_def_op.deref(ctx).get_result(0),
        dual_def_op.deref(ctx).get_result(1),
    );
    let (module_op, func_op, const_op, ret_op) = const_ret_in_mod(ctx).unwrap();
    dual_def_op.insert_before(ctx, ret_op.get_operation());
    const_op
        .get_result(ctx)
        .replace_some_uses_with(ctx, |_, _| true, &res1);
    res1.replace_some_uses_with(ctx, |_, _| true, &res2);
    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar {
          ^block_1v1():
            builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
              ^entry_block_2v1():
                c0_op_4v1_res0 = test.constant builtin.integer <0x0: builtin.int<si64>>;
                op_1v1_res0, op_1v1_res1 = test.dual_def () [] []: <() -> (builtin.int<si64>, builtin.int<si64>)>;
                test.return op_1v1_res1
            }
        }"#]]
    .assert_eq(&printed);

    let dual_arg_block = BasicBlock::new(ctx, None, vec![u64_ty, u64_ty]);
    let (arg1, arg2) = (
        dual_arg_block.deref(ctx).get_argument(0),
        dual_arg_block.deref(ctx).get_argument(1),
    );
    dual_arg_block.insert_after(ctx, func_op.get_entry_block(ctx));
    let ret_op = ReturnOp::new(ctx, arg1);
    ret_op.get_operation().insert_at_back(dual_arg_block, ctx);
    arg1.replace_some_uses_with(ctx, |_, _| true, &arg2);

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar {
          ^block_1v1():
            builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
              ^entry_block_2v1():
                c0_op_4v1_res0 = test.constant builtin.integer <0x0: builtin.int<si64>>;
                op_1v1_res0, op_1v1_res1 = test.dual_def () [] []: <() -> (builtin.int<si64>, builtin.int<si64>)>;
                test.return op_1v1_res1
              ^block_3v1(block_3v1_arg0:builtin.int<si64>,block_3v1_arg1:builtin.int<si64>):
                test.return block_3v1_arg1
            }
        }"#]]
    .assert_eq(&printed);
}

#[test]
/// A test to just print a constructed IR to stdout.
fn print_simple() -> Result<()> {
    let ctx = &mut setup_context_dialects();
    let module_op = const_ret_in_mod(ctx)?.0.get_operation();
    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar {
          ^block_1v1():
            builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
              ^entry_block_2v1():
                c0_op_3v1_res0 = test.constant builtin.integer <0x0: builtin.int<si64>>;
                test.return c0_op_3v1_res0
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
                c0_op_2_0_res0 = test.constant builtin.integer <0x0: builtin.int <si64>>;
                test.return c0_op_2_0_res0
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
                c0_op_2_0_res0 = test.constant builtin.integer <0x0: builtin.int <si64>>;
                c0_op_2_0_res0 = test.constant builtin.integer <0x0: builtin.int <si64>>;
                test.return c0_op_2_0_res0
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
                c0_op_2_0_res0 = test.constant builtin.integer <0x0: builtin.int <si64>>;
                test.return c0_op_2_0_res0
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
                test.return c0_op_2_0_res0
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
                c0_op_2_0_res0 = test.constant builtin.integer <0x0: builtin.int <si64>>;
                test.return c0_op_2_0_res0
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

#[test]
fn test_preorder_forward_walk() {
    let ctx = &mut setup_context_dialects();
    let module_op = const_ret_in_mod(ctx).unwrap().0.get_operation();

    let mut state = Vec::new();

    walkers::walk_op(
        ctx,
        &mut state,
        &WALKCONFIG_PREORDER_FORWARD,
        module_op,
        |_ctx, state, node| {
            if let IRNode::Operation(op) = node {
                state.push(op);
            }
        },
    );

    let ops = state.into_iter().fold("".to_string(), |accum, op| {
        accum + &op.disp(ctx).to_string() + "\n"
    });
    expect![[r#"
        builtin.module @bar {
          ^block_1v1():
            builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
              ^entry_block_2v1():
                c0_op_3v1_res0 = test.constant builtin.integer <0x0: builtin.int<si64>>;
                test.return c0_op_3v1_res0
            }
        }
        builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
          ^entry_block_2v1():
            c0_op_3v1_res0 = test.constant builtin.integer <0x0: builtin.int<si64>>;
            test.return c0_op_3v1_res0
        }
        c0_op_3v1_res0 = test.constant builtin.integer <0x0: builtin.int<si64>>
        test.return c0_op_3v1_res0
    "#]]
    .assert_eq(&ops);
}

#[test]
fn test_postorder_forward_walk() {
    let ctx = &mut setup_context_dialects();
    let module_op = const_ret_in_mod(ctx).unwrap().0.get_operation();

    let mut state = Vec::new();

    walkers::walk_op(
        ctx,
        &mut state,
        &WALKCONFIG_POSTORDER_FORWARD,
        module_op,
        |_ctx, state, node| {
            if let IRNode::Operation(op) = node {
                state.push(op);
            }
        },
    );

    let ops = state.into_iter().fold("".to_string(), |accum, op| {
        accum + &op.disp(ctx).to_string() + "\n"
    });
    expect![[r#"
        c0_op_3v1_res0 = test.constant builtin.integer <0x0: builtin.int<si64>>
        test.return c0_op_3v1_res0
        builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
          ^entry_block_2v1():
            c0_op_3v1_res0 = test.constant builtin.integer <0x0: builtin.int<si64>>;
            test.return c0_op_3v1_res0
        }
        builtin.module @bar {
          ^block_1v1():
            builtin.func @foo: builtin.function<() -> (builtin.int<si64>)> {
              ^entry_block_2v1():
                c0_op_3v1_res0 = test.constant builtin.integer <0x0: builtin.int<si64>>;
                test.return c0_op_3v1_res0
            }
        }
    "#]]
    .assert_eq(&ops);
}

#[test]
fn test_walker_find_op() {
    let ctx = &mut setup_context_dialects();
    let (module_op, _, const_op, _) = const_ret_in_mod(ctx).unwrap();

    let const1_op = ConstantOp::new(ctx, 1);
    const1_op
        .get_operation()
        .insert_after(ctx, const_op.get_operation());
    set_operation_result_name(ctx, const1_op.get_operation(), 0, "c1".to_string());

    // A function to breaks the walk when a [ConstantOp] is found.
    fn finder(
        ctx: &mut Context,
        _: &mut (),
        node: IRNode,
    ) -> interruptible::WalkResult<ConstantOp> {
        if let IRNode::Operation(op) = node {
            if let Some(const_op) = Operation::get_op(op, ctx).downcast_ref::<ConstantOp>() {
                return walk_break(*const_op);
            }
        }
        walk_advance()
    }

    let res1 = walkers::interruptible::walk_op(
        ctx,
        &mut (),
        &WALKCONFIG_PREORDER_FORWARD,
        module_op.get_operation(),
        finder,
    );
    assert!(matches!(res1, interruptible::WalkResult::Break(c) if c == const_op));

    let res2 = walkers::interruptible::walk_op(
        ctx,
        &mut (),
        &WALKCONFIG_POSTORDER_REVERSE,
        module_op.get_operation(),
        finder,
    );
    assert!(matches!(res2, interruptible::WalkResult::Break(c) if c == const1_op));
}
