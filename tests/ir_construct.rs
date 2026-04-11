use common::{ConstantOp, ReturnOp};
use expect_test::{Expect, expect};
use pliron::basic_block::BasicBlockVerifyErr;
use pliron::builtin::attributes::StringAttr;
use pliron::context::Ptr;
use pliron::derive::pliron_op;
use pliron::dict_key;
use pliron::op::verify_op;
use pliron::operation::verify_operation;
use pliron::{
    basic_block::BasicBlock,
    builtin::{
        op_interfaces::OneResultInterface,
        types::{IntegerType, Signedness},
    },
    context::Context,
    debug_info::set_operation_result_name,
    graph::walkers::{
        self, IRNode, WALKCONFIG_POSTORDER_FORWARD, WALKCONFIG_POSTORDER_REVERSE,
        WALKCONFIG_PREORDER_FORWARD,
        interruptible::{self, walk_advance, walk_break},
    },
    irfmt::parsers::spaced,
    location,
    op::Op,
    operation::Operation,
    parsable::{self, state_stream_from_iterator},
    printable::Printable,
    result::Result,
};

use crate::common::const_ret_in_mod;
use combine::parser::Parser;

#[cfg(target_family = "wasm")]
use wasm_bindgen_test::*;

mod common;

// Test erasing the entire top module.
#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn construct_and_erase() -> Result<()> {
    let ctx = &mut Context::new();
    let module_op = const_ret_in_mod(ctx)?.0.get_operation();
    Operation::erase(module_op, ctx);
    assert!(ctx.is_ir_empty());
    Ok(())
}

// Ensure that erasing an op with uses panics.
#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
#[should_panic(expected = "Operation with use(s) being erased")]
fn removed_used_op() {
    let ctx = &mut Context::new();

    // const_ret_in_mod builds a module with a function.
    let (_, _, const_op, _) = const_ret_in_mod(ctx).unwrap();

    // const_op is used in the return. Erasing it must panic.
    Operation::erase(const_op.get_operation(), ctx);
}

// Testing replacing all uses of c0 with c1.
#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn replace_c0_with_c1() -> Result<()> {
    let ctx = &mut Context::new();

    // const_ret_in_mod builds a module with a function.
    let (module_op, _, const_op, _) = const_ret_in_mod(ctx).unwrap();

    let const1_op = ConstantOp::new(ctx, 1);
    const1_op
        .get_operation()
        .insert_after(ctx, const_op.get_operation());
    set_operation_result_name(ctx, const1_op.get_operation(), 0, "c1".try_into().unwrap());
    let const0_val = const_op.get_result(ctx);
    const0_val.replace_some_uses_with(ctx, |_, _| true, &const1_op.get_result(ctx));

    Operation::erase(const_op.get_operation(), ctx);

    verify_op(&module_op, ctx)?;

    Ok(())
}

// Replace ret_op's first operand (which is c0) with c1.
// Erase c0. Verify.
#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn replace_c0_with_c1_operand() -> Result<()> {
    let ctx = &mut Context::new();

    // const_ret_in_mod builds a module with a function.
    let (module_op, _, const_op, ret_op) = const_ret_in_mod(ctx).unwrap();

    let const1_op = ConstantOp::new(ctx, 1);
    const1_op
        .get_operation()
        .insert_after(ctx, const_op.get_operation());
    set_operation_result_name(ctx, const1_op.get_operation(), 0, "c1".try_into().unwrap());

    let printed = format!("{}", module_op.get_operation().disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0;
                c1_op5v1_res0 = test.constant builtin.integer <1: si64> !1;
                test.return c0_op3v1_res0
            }
        }

        outlined_attributes:
        !0 = [builtin_debug_info = builtin.debug_info [c0]]
        !1 = [builtin_debug_info = builtin.debug_info [c1]]
    "#]]
    .assert_eq(&printed);

    Operation::replace_operand(ret_op.get_operation(), ctx, 0, const1_op.get_result(ctx));
    Operation::erase(const_op.get_operation(), ctx);

    let printed = format!("{}", module_op.get_operation().disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                c1_op5v1_res0 = test.constant builtin.integer <1: si64> !0;
                test.return c1_op5v1_res0
            }
        }

        outlined_attributes:
        !0 = [builtin_debug_info = builtin.debug_info [c1]]
    "#]]
    .assert_eq(&printed);

    verify_op(&module_op, ctx)?;

    Ok(())
}

#[pliron_op(name = "test.dual_def", format, verifier = "succ")]
struct DualDefOp {}

/// If an Op has multiple results, or a block multiple args,
/// replacing all uses of one with the other should work.
/// (since our RefCell is at the Op or block level, we shouldn't
/// end up with a multiple borrow panic).
#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn test_replace_within_same_def_site() {
    let ctx = &mut Context::new();

    let u64_ty = IntegerType::get(ctx, 64, Signedness::Signed).into();

    let dual_def_op = Operation::new(
        ctx,
        DualDefOp::get_concrete_op_info(),
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
    let printed = format!("{}", module_op.get_operation().disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                c0_op4v1_res0 = test.constant builtin.integer <0: si64> !0;
                op1v1_res0, op1v1_res1 = test.dual_def () [] []: <() -> (builtin.integer si64, builtin.integer si64)>;
                test.return op1v1_res1
            }
        }

        outlined_attributes:
        !0 = [builtin_debug_info = builtin.debug_info [c0]]
    "#]]
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

    let printed = format!("{}", module_op.get_operation().disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                c0_op4v1_res0 = test.constant builtin.integer <0: si64> !0;
                op1v1_res0, op1v1_res1 = test.dual_def () [] []: <() -> (builtin.integer si64, builtin.integer si64)>;
                test.return op1v1_res1

              ^block3v1(block3v1_arg0: builtin.integer si64, block3v1_arg1: builtin.integer si64):
                test.return block3v1_arg1
            }
        }

        outlined_attributes:
        !0 = [builtin_debug_info = builtin.debug_info [c0]]
    "#]]
    .assert_eq(&printed);
}

#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
/// A test to just print a constructed IR to stdout.
fn print_simple() -> Result<()> {
    let ctx = &mut Context::new();
    let module_op = const_ret_in_mod(ctx)?.0.get_operation();
    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0;
                test.return c0_op3v1_res0
            }
        }

        outlined_attributes:
        !0 = [builtin_debug_info = builtin.debug_info [c0]]
    "#]]
    .assert_eq(&printed);
    println!("{printed}");
    Ok(())
}

#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn parse_simple() -> Result<()> {
    let input = r#"
        builtin.module @bar {
        ^block_0_0():
            builtin.func @foo: builtin.function <() -> (builtin.integer si64)> {
            ^entry_block_1_0():
                c0_op_2_0_res0 = test.constant builtin.integer <0: si64>;
                test.return c0_op_2_0_res0
            ^exit(a : builtin.integer si32):
            }
        }"#;

    let ctx = &mut Context::new();
    let op = {
        let state_stream = state_stream_from_iterator(
            input.chars(),
            parsable::State::new(ctx, location::Source::InMemory),
        );
        spaced(Operation::top_level_parser())
            .parse(state_stream)
            .unwrap()
            .0
    };
    println!("{}", op.disp(ctx));
    Ok(())
}

dict_key!(ATTR_KEY_TEST_ON_FUNC_VALUE, "test_on_func_value");
dict_key!(ATTR_KEY_BLOCK_TEST, "block_test_attr");

#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn parse_function_with_attrs() -> Result<()> {
    let ctx = &mut Context::new();
    let (module_op, _, _const_op, ret_op) = const_ret_in_mod(ctx).unwrap();

    let func_op = ret_op
        .get_operation()
        .deref(ctx)
        .get_parent_op(ctx)
        .unwrap();
    func_op.deref_mut(ctx).attributes.set(
        ATTR_KEY_TEST_ON_FUNC_VALUE.clone(),
        StringAttr::new("func_attr_value".into()),
    );

    let printed = format!("{}", module_op.get_operation().disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
              [test_on_func_value: builtin.string "func_attr_value"]
            {
              ^entry_block2v1():
                c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0;
                test.return c0_op3v1_res0
            }
        }

        outlined_attributes:
        !0 = [builtin_debug_info = builtin.debug_info [c0]]
    "#]]
    .assert_eq(&printed);

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let parsed = spaced(Operation::top_level_parser())
        .parse(state_stream)
        .unwrap()
        .0;

    let print_parsed = format!("{}", parsed.disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1_block4v1() !0:
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
              [test_on_func_value: builtin.string "func_attr_value"]
            {
              ^entry_block2v1_block3v1() !1:
                c0_op7v1_res0 = test.constant builtin.integer <0: si64> !2;
                test.return c0_op7v1_res0 !3
            } !4
        } !5

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 3], []
        !1 = @[<in-memory>: line: 7, column: 7], []
        !2 = @[<in-memory>: line: 8, column: 9], [builtin_debug_info = builtin.debug_info [c0]]
        !3 = @[<in-memory>: line: 9, column: 9], []
        !4 = @[<in-memory>: line: 4, column: 5], []
        !5 = @[<in-memory>: line: 1, column: 1], []
    "#]]
    .assert_eq(&print_parsed);

    Ok(())
}

fn expect_parse_error(input: &str, expected_err: Expect) {
    let ctx = &mut Context::new();
    let state_stream = state_stream_from_iterator(
        input.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let actual_err = spaced(Operation::top_level_parser())
        .parse(state_stream)
        .err()
        .unwrap();

    expected_err.assert_eq(&actual_err.to_string());
}

#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn parse_err_multiple_def() {
    let input_multiple_ssa_defs = r#"
        builtin.module @bar {
        ^block_0_0():
            builtin.func @foo: builtin.function <() -> (builtin.integer si64)> {
            ^entry_block_1_0():
                c0_op_2_0_res0 = test.constant builtin.integer <0 : si64>;
                c0_op_2_0_res0 = test.constant builtin.integer <0 : si64>;
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
            builtin.func @foo: builtin.function <() -> (builtin.integer si64)> {
            ^entry_block_1_0():
                c0_op_2_0_res0 = test.constant builtin.integer <0: si64>;
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
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn parse_err_unresolved_def() {
    let input_multiple_defs = r#"
        builtin.module @bar {
        ^block_0_0():
            builtin.func @foo: builtin.function <() -> (builtin.integer si64)> {
            ^entry_block_1_0():
                test.return c0_op_2_0_res0
            }
        }"#;

    let expected_err = expect![[r#"
        Parse error at line: 4, column: 80
        Identifier c0_op_2_0_res0 was not resolved to any definition in the scope
    "#]];
    expect_parse_error(input_multiple_defs, expected_err);
}

#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn parse_err_block_label_colon() {
    let input_label_colon_missing = r#"
        builtin.module @bar {
        ^block_0_0():
            builtin.func @foo: builtin.function <() -> (builtin.integer si64)> {
            ^entry_block_1_0():
                c0_op_2_0_res0 = test.constant builtin.integer <0: si64>;
                test.return c0_op_2_0_res0
            ^exit()
            }
        }"#;

    let expected_err = expect![[r#"
        Parse error at line: 9, column: 13
        Unexpected `}`
        Expected whitespaces or `:`
    "#]];

    expect_parse_error(input_label_colon_missing, expected_err);
}

#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn parse_err_block_args() {
    let input_label_colon_missing = r#"
        builtin.module @bar {
        ^block_0_0(a : builtin.integer si32, b):
        }"#;

    let expected_err = expect![[r#"
        Parse error at line: 3, column: 47
        Unexpected `)`
        Expected whitespaces or `:`
    "#]];

    expect_parse_error(input_label_colon_missing, expected_err);
}

#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn test_preorder_forward_walk() {
    let ctx = &mut Context::new();
    let module_op = const_ret_in_mod(ctx).unwrap().0.get_operation();

    let mut state = Vec::new();

    walkers::uninterruptible::immutable::walk_op(
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
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0;
                test.return c0_op3v1_res0
            }
        }

        outlined_attributes:
        !0 = [builtin_debug_info = builtin.debug_info [c0]]

        builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
        {
          ^entry_block2v1():
            c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0;
            test.return c0_op3v1_res0
        }
        c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0
        test.return c0_op3v1_res0
    "#]]
    .assert_eq(&ops);

    Operation::erase(module_op, ctx);
    assert!(ctx.is_ir_empty());
}

#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn walker_print() {
    let ctx = &mut Context::new();
    let module_op = const_ret_in_mod(ctx).unwrap().0.get_operation();

    fn print_op(
        ctx: &Context,
        root: Ptr<Operation>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        struct State<'a, 'b> {
            f: &'a mut std::fmt::Formatter<'b>,
        }
        let mut state = State { f };
        match walkers::interruptible::immutable::walk_op(
            ctx,
            &mut state,
            &WALKCONFIG_PREORDER_FORWARD,
            root,
            |ctx, state, node| {
                if let IRNode::Operation(op) = node {
                    match writeln!(state.f, "{}", op.disp(ctx)) {
                        Ok(_) => return walk_advance(),
                        Err(e) => return walk_break(e),
                    }
                }
                walk_advance()
            },
        ) {
            interruptible::WalkResult::Continue(_) => Ok(()),
            interruptible::WalkResult::Break(e) => Err(e),
        }
    }

    struct OpPrinter {
        root: Ptr<Operation>,
    }
    impl Printable for OpPrinter {
        fn fmt(
            &self,
            ctx: &Context,
            _state: &pliron::printable::State,
            f: &mut std::fmt::Formatter<'_>,
        ) -> std::fmt::Result {
            print_op(ctx, self.root, f)
        }
    }
    let op_printer = OpPrinter { root: module_op };
    let printed = format!("{}", op_printer.disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0;
                test.return c0_op3v1_res0
            }
        }

        outlined_attributes:
        !0 = [builtin_debug_info = builtin.debug_info [c0]]

        builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
        {
          ^entry_block2v1():
            c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0;
            test.return c0_op3v1_res0
        }
        c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0
        test.return c0_op3v1_res0
    "#]]
    .assert_eq(&printed);
}

#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn test_postorder_forward_walk() {
    let ctx = &mut Context::new();
    let module_op = const_ret_in_mod(ctx).unwrap().0.get_operation();

    let mut state = Vec::new();

    walkers::uninterruptible::immutable::walk_op(
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
        c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0
        test.return c0_op3v1_res0
        builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
        {
          ^entry_block2v1():
            c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0;
            test.return c0_op3v1_res0
        }
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0;
                test.return c0_op3v1_res0
            }
        }

        outlined_attributes:
        !0 = [builtin_debug_info = builtin.debug_info [c0]]

    "#]]
    .assert_eq(&ops);
}

#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn test_walker_find_op() {
    let ctx = &mut Context::new();
    let (module_op, _, const_op, _) = const_ret_in_mod(ctx).unwrap();

    let const1_op = ConstantOp::new(ctx, 1);
    const1_op
        .get_operation()
        .insert_after(ctx, const_op.get_operation());
    set_operation_result_name(ctx, const1_op.get_operation(), 0, "c1".try_into().unwrap());

    // A function to breaks the walk when a [ConstantOp] is found.
    fn finder(ctx: &Context, _: &mut (), node: IRNode) -> interruptible::WalkResult<ConstantOp> {
        if let IRNode::Operation(op) = node
            && let Some(const_op) = Operation::get_op::<ConstantOp>(op, ctx)
        {
            return walk_break(const_op);
        }
        walk_advance()
    }

    let res1 = walkers::interruptible::immutable::walk_op(
        ctx,
        &mut (),
        &WALKCONFIG_PREORDER_FORWARD,
        module_op.get_operation(),
        finder,
    );
    assert!(matches!(res1, interruptible::WalkResult::Break(c) if c == const_op));

    let res2 = walkers::interruptible::immutable::walk_op(
        ctx,
        &mut (),
        &WALKCONFIG_POSTORDER_REVERSE,
        module_op.get_operation(),
        finder,
    );
    assert!(matches!(res2, interruptible::WalkResult::Break(c) if c == const1_op));
}

#[test]
fn test_verify_missing_terminator() -> Result<()> {
    let ctx = &mut Context::new();
    let (module_op, _, _, ret_op) = const_ret_in_mod(ctx)?;

    verify_op(&module_op, ctx)?;

    Operation::erase(ret_op.get_operation(), ctx);

    let verify_res = verify_op(&module_op, ctx);
    let err = verify_res.unwrap_err();
    let err = err.err.downcast_ref::<BasicBlockVerifyErr>().unwrap();
    assert!(matches!(err, BasicBlockVerifyErr::MissingTerminator(_)));

    Ok(())
}

#[test]
fn test_verify_multiple_terminator() -> Result<()> {
    let ctx = &mut Context::new();
    let (module_op, _, const_op, ret_op) = const_ret_in_mod(ctx)?;

    verify_op(&module_op, ctx)?;

    let ret2_op = ReturnOp::new(ctx, const_op.get_result(ctx));
    ret2_op
        .get_operation()
        .insert_before(ctx, ret_op.get_operation());

    let verify_res = verify_op(&module_op, ctx);
    let err = verify_res.unwrap_err();
    let err = err.err.downcast_ref::<BasicBlockVerifyErr>().unwrap();
    assert!(matches!(err, BasicBlockVerifyErr::TerminatorNotLast(_)));

    Ok(())
}

#[test]
fn block_inline_attrs_print() -> Result<()> {
    let ctx = &mut Context::new();
    let (module_op, func_op, _const_op, _ret_op) = const_ret_in_mod(ctx)?;

    let entry_block = func_op.get_entry_block(ctx);

    // Set an inline attribute on the block
    entry_block.deref_mut(ctx).attributes.set(
        ATTR_KEY_BLOCK_TEST.clone(),
        StringAttr::new("test_value".into()),
    );

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1() [block_test_attr: builtin.string "test_value"]:
                c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0;
                test.return c0_op3v1_res0
            }
        }"#]]
    .assert_eq(&printed);

    Ok(())
}

#[test]
fn block_inline_attrs_roundtrip() -> Result<()> {
    let input = r#"
        builtin.module @bar {
        ^block_0_0():
            builtin.func @foo: builtin.function <() -> (builtin.integer si64)> {
            ^entry_block_1_0() [block_attr: builtin.string "hello"]:
                c0_op_2_0_res0 = test.constant builtin.integer <0: si64>;
                test.return c0_op_2_0_res0
            }
        }"#;

    let ctx = &mut Context::new();
    let op = {
        let state_stream = state_stream_from_iterator(
            input.chars(),
            parsable::State::new(ctx, location::Source::InMemory),
        );
        spaced(Operation::top_level_parser())
            .parse(state_stream)
            .unwrap()
            .0
    };

    verify_operation(op, ctx)?;

    let printed = format!("{}", op.disp(ctx));

    // Parse again and print to confirm roundtrip
    let ctx2 = &mut Context::new();
    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx2, location::Source::InMemory),
    );
    let parsed2 = spaced(Operation::top_level_parser())
        .parse(state_stream)
        .unwrap()
        .0;

    verify_operation(parsed2, ctx2)?;

    Ok(())
}

#[test]
fn block_multiple_inline_attrs() -> Result<()> {
    let ctx = &mut Context::new();
    let (module_op, func_op, _const_op, _ret_op) = const_ret_in_mod(ctx)?;

    // Get the function's entry block and set attributes on it
    let func_entry_block = func_op.get_entry_block(ctx);

    // Set multiple inline attributes on the function's entry block
    func_entry_block.deref_mut(ctx).attributes.set(
        "attr1".try_into().unwrap(),
        StringAttr::new("value1".into()),
    );
    func_entry_block.deref_mut(ctx).attributes.set(
        "attr2".try_into().unwrap(),
        StringAttr::new("value2".into()),
    );

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1() [attr1: builtin.string "value1", attr2: builtin.string "value2"]:
                c0_op3v1_res0 = test.constant builtin.integer <0: si64> !0;
                test.return c0_op3v1_res0
            }
        }"#]]
    .assert_eq(&printed);

    Ok(())
}

#[test]
fn block_attrs_parse_roundtrip() -> Result<()> {
    // Test that block inline attributes survive a parse-print-parse roundtrip.
    let input = r#"
        builtin.module @bar {
        ^block_0_0():
            builtin.func @foo: builtin.function <() -> (builtin.integer si64)> {
            ^entry_block_1_0() [block_attr: builtin.string "hello"]:
                c0_op_2_0_res0 = test.constant builtin.integer <0: si64>;
                test.return c0_op_2_0_res0
            }
        }"#;

    let ctx = &mut Context::new();
    let op = {
        let state_stream = state_stream_from_iterator(
            input.chars(),
            parsable::State::new(ctx, location::Source::InMemory),
        );
        spaced(Operation::top_level_parser())
            .parse(state_stream)
            .unwrap()
            .0
    };

    verify_operation(op, ctx)?;

    let printed = format!("{}", op.deref(ctx).disp(ctx));

    // After parsing from source, blocks get locations. Second print has outline indices.
    // The outlined_attributes section only has locations; inline (non-outlined) attrs stay inline.
    expect![[r#"
        builtin.module @bar 
        {
          ^block_0_0_block2v1() !0:
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block_1_0_block1v1() [block_attr: builtin.string "hello"] !1:
                c0_op_2_0_res0_op3v1_res0 = test.constant builtin.integer <0: si64> !2;
                test.return c0_op_2_0_res0_op3v1_res0 !3
            } !4
        } !5

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 9], []
        !1 = @[<in-memory>: line: 5, column: 13], []
        !2 = @[<in-memory>: line: 6, column: 17], [builtin_debug_info = builtin.debug_info [c0_op_2_0_res0]]
        !3 = @[<in-memory>: line: 7, column: 17], []
        !4 = @[<in-memory>: line: 4, column: 13], []
        !5 = @[<in-memory>: line: 2, column: 9], []
    "#]]
    .assert_eq(&printed);

    // Parse again and verify it's still valid
    let ctx2 = &mut Context::new();
    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx2, location::Source::InMemory),
    );
    let parsed2 = spaced(Operation::top_level_parser())
        .parse(state_stream)
        .unwrap()
        .0;

    verify_operation(parsed2, ctx2)?;

    // The third print should still have the attributes
    let print3 = format!("{}", parsed2.deref(ctx2).disp(ctx2));
    expect![[r#"
        builtin.module @bar 
        {
          ^block_0_0_block2v1_block2v1() !0:
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block_1_0_block1v1_block1v1() [block_attr: builtin.string "hello"] !1:
                c0_op_2_0_res0_op3v1_res0 = test.constant builtin.integer <0: si64> !2;
                test.return c0_op_2_0_res0_op3v1_res0 !3
            } !4
        } !5

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 9], []
        !1 = @[<in-memory>: line: 5, column: 13], []
        !2 = @[<in-memory>: line: 6, column: 17], [builtin_debug_info = builtin.debug_info [c0_op_2_0_res0]]
        !3 = @[<in-memory>: line: 7, column: 17], []
        !4 = @[<in-memory>: line: 4, column: 13], []
        !5 = @[<in-memory>: line: 2, column: 9], []
    "#]]
    .assert_eq(&print3);

    Ok(())
}
