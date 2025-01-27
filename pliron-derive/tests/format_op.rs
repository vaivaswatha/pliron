//! Test format derive for `Op`s.

use expect_test::expect;
use pliron::{
    builtin::op_interfaces::{
        OneOpdInterface, OneRegionInterface, OneResultInterface, ZeroOpdInterface,
        ZeroResultInterface,
    },
    common_traits::Verify,
    impl_verify_succ, location,
    op::Op,
    operation::Operation,
    parsable::{self, state_stream_from_iterator, Parsable},
    printable::Printable,
};
use pliron_derive::{def_op, derive_op_interface_impl, format_op};
mod common;
use common::setup_context_dialects;

#[format_op("")]
#[def_op("test.zero_results_zero_operands")]
#[derive_op_interface_impl(ZeroOpdInterface, ZeroResultInterface)]
struct ZeroResultsZeroOperandsOp {}
impl_verify_succ!(ZeroResultsZeroOperandsOp);

#[test]
fn zero_results_zero_operands() {
    let ctx = &mut setup_context_dialects();
    ZeroResultsZeroOperandsOp::register(ctx, ZeroResultsZeroOperandsOp::parser_fn);

    let op = Operation::new(
        ctx,
        ZeroResultsZeroOperandsOp::get_opid_static(),
        vec![],
        vec![],
        vec![],
        0,
    );
    let printed = op.disp(ctx).to_string();
    assert_eq!("test.zero_results_zero_operands ", &printed);

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let (res, _) = Operation::parser(())
        .parse(state_stream)
        .expect("ZeroResultsZeroOperands parser failed");
    assert_eq!(res.disp(ctx).to_string(), printed);

    assert!(res.verify(ctx).is_ok());
}

#[format_op("`:` type($0)")]
#[def_op("test.one_result_zero_operands")]
#[derive_op_interface_impl(ZeroOpdInterface, OneResultInterface)]
struct OneResultZeroOperandsOp {}
impl_verify_succ!(OneResultZeroOperandsOp);

#[test]
fn one_result_zero_operands() {
    let ctx = &mut setup_context_dialects();
    OneResultZeroOperandsOp::register(ctx, OneResultZeroOperandsOp::parser_fn);

    let printed = "builtin.func @testfunc : builtin.function <() -> ()> {
          ^entry():
            res0 = test.one_result_zero_operands : builtin.int <si64>;
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::parser(())
        .parse(state_stream)
        .expect("OneResultZeroOperands parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <() -> ()> 
        {
          ^entry_block_1v1():
            res0_op_3v1_res0 = test.one_result_zero_operands :builtin.int <si64>;
            test.return res0_op_3v1_res0
        }"#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[format_op("$0 `:` type($0)")]
#[def_op("test.one_result_one_operand")]
#[derive_op_interface_impl(OneOpdInterface, OneResultInterface)]
struct OneResultOneOperandOp {}
impl_verify_succ!(OneResultOneOperandOp);

#[test]
fn one_result_one_operand() {
    let ctx = &mut setup_context_dialects();
    OneResultZeroOperandsOp::register(ctx, OneResultZeroOperandsOp::parser_fn);
    OneResultOneOperandOp::register(ctx, OneResultOneOperandOp::parser_fn);

    let printed = "builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry():
            res0 = test.one_result_zero_operands : builtin.int <si64>;
            res1 = test.one_result_one_operand res0 : builtin.int <si64>;
            test.return res1
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::parser(())
        .parse(state_stream)
        .expect("OneResultOneOperand parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <() -> ()> 
        {
          ^entry_block_1v1():
            res0_op_3v1_res0 = test.one_result_zero_operands :builtin.int <si64>;
            res1_op_4v1_res0 = test.one_result_one_operand res0_op_3v1_res0:builtin.int <si64>;
            test.return res1_op_4v1_res0
        }"#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[format_op("$0 `,` $1 `:` `(` type($0) `,` type($1) `)`")]
#[def_op("test.two_results_two_operands")]
struct TwoResultsTwoOperandsOp {}
impl_verify_succ!(TwoResultsTwoOperandsOp);

#[test]
fn two_result_two_operands() {
    let ctx = &mut setup_context_dialects();
    OneResultZeroOperandsOp::register(ctx, OneResultZeroOperandsOp::parser_fn);
    TwoResultsTwoOperandsOp::register(ctx, TwoResultsTwoOperandsOp::parser_fn);

    let printed = "builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry():
            res0 = test.one_result_zero_operands :builtin.int <si64>;
            res1a, res1b = test.two_results_two_operands res0, res0 : (builtin.int <si64>, builtin.int <si64>);
            test.return res1a
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::parser(())
        .parse(state_stream)
        .expect("TwoResultTwoOperands parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <() -> ()> 
        {
          ^entry_block_1v1():
            res0_op_3v1_res0 = test.one_result_zero_operands :builtin.int <si64>;
            res1a_op_4v1_res0, res1b_op_4v1_res1 = test.two_results_two_operands res0_op_3v1_res0,res0_op_3v1_res0:(builtin.int <si64>,builtin.int <si64>);
            test.return res1a_op_4v1_res0
        }"#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

use pliron::builtin::attributes::IntegerAttr;

#[format_op("attr($attr, $IntegerAttr) `:` type($0)")]
#[def_op("test.attr_op")]
struct AttrOp {}
impl_verify_succ!(AttrOp);

#[test]
fn attr_op() {
    let ctx = &mut setup_context_dialects();
    AttrOp::register(ctx, AttrOp::parser_fn);

    let printed = "builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry():
            res0 = test.attr_op <0x0: builtin.int <si64>> :builtin.int <si64>;
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::parser(())
        .parse(state_stream)
        .expect("AttrOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <() -> ()> 
        {
          ^entry_block_1v1():
            res0_op_3v1_res0 = test.attr_op <0x0: builtin.int <si64>>:builtin.int <si64>;
            test.return res0_op_3v1_res0
        }"#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[format_op("attr($attr, `pliron::builtin::attributes::StringAttr`) `:` type($0)")]
#[def_op("test.attr_op2")]
struct AttrOp2 {}
impl_verify_succ!(AttrOp2);

#[test]
fn attr_op2() {
    let ctx = &mut setup_context_dialects();
    AttrOp2::register(ctx, AttrOp2::parser_fn);

    let printed = "builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry():
            res0 = test.attr_op2 \"Hello World\" :builtin.int <si64>;
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::parser(())
        .parse(state_stream)
        .expect("AttrOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <() -> ()> 
        {
          ^entry_block_1v1():
            res0_op_3v1_res0 = test.attr_op2 "Hello World":builtin.int <si64>;
            test.return res0_op_3v1_res0
        }"#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[format_op("$attr `:` type($0)")]
#[def_op("test.attr_op3")]
struct AttrOp3 {}
impl_verify_succ!(AttrOp3);

#[test]
fn attr_op3() {
    let ctx = &mut setup_context_dialects();
    AttrOp3::register(ctx, AttrOp3::parser_fn);

    let printed = "builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry():
            res0 = test.attr_op3 builtin.integer <0x0: builtin.int <si64>> :builtin.int <si64>;
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::parser(())
        .parse(state_stream)
        .expect("AttrOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <() -> ()> 
        {
          ^entry_block_1v1():
            res0_op_3v1_res0 = test.attr_op3 builtin.integer <0x0: builtin.int <si64>>:builtin.int <si64>;
            test.return res0_op_3v1_res0
        }"#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[format_op("`(`$0`)` region($0)")]
#[def_op("test.if_op")]
#[derive_op_interface_impl(OneOpdInterface, ZeroResultInterface, OneRegionInterface)]
struct IfOp {}
impl_verify_succ!(IfOp);

#[test]
fn if_op() {
    let ctx = &mut setup_context_dialects();
    AttrOp::register(ctx, AttrOp::parser_fn);
    IfOp::register(ctx, IfOp::parser_fn);

    let printed = "builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry():
            res0 = test.attr_op <0x0: builtin.int <si64>> :builtin.int <si64>;
            test.if_op (res0) {
              ^then():
                res1 = test.attr_op <0x1: builtin.int <si64>> :builtin.int <si64>;
                test.return res1
            };
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::parser(())
        .parse(state_stream)
        .expect("IfOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <() -> ()> 
        {
          ^entry_block_2v1():
            res0_op_3v1_res0 = test.attr_op <0x0: builtin.int <si64>>:builtin.int <si64>;
            test.if_op (res0_op_3v1_res0)
            {
              ^then_block_1v1():
                res1_op_4v1_res0 = test.attr_op <0x1: builtin.int <si64>>:builtin.int <si64>;
                test.return res1_op_4v1_res0
            };
            test.return res0_op_3v1_res0
        }"#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[format_op("`(`$0`)` region($0) `else` region($1)")]
#[def_op("test.if_else_op")]
#[derive_op_interface_impl(OneOpdInterface, ZeroResultInterface)]
struct IfElseOp {}
impl_verify_succ!(IfElseOp);

#[test]
fn if_else_op() {
    let ctx = &mut setup_context_dialects();
    AttrOp::register(ctx, AttrOp::parser_fn);
    IfElseOp::register(ctx, IfElseOp::parser_fn);

    let printed = "builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry():
            res0 = test.attr_op <0x0: builtin.int <si64>> :builtin.int <si64>;
            test.if_else_op (res0) {
              ^then():
                res1 = test.attr_op <0x1: builtin.int <si64>> :builtin.int <si64>;
                test.return res1
            } else {
              ^else():
                res2 = test.attr_op <0x2: builtin.int <si64>> :builtin.int <si64>;
                test.return res2
            };
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::parser(())
        .parse(state_stream)
        .expect("IfOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <() -> ()> 
        {
          ^entry_block_3v1():
            res0_op_3v1_res0 = test.attr_op <0x0: builtin.int <si64>>:builtin.int <si64>;
            test.if_else_op (res0_op_3v1_res0)
            {
              ^then_block_1v1():
                res1_op_4v1_res0 = test.attr_op <0x1: builtin.int <si64>>:builtin.int <si64>;
                test.return res1_op_4v1_res0
            }else
            {
              ^else_block_2v1():
                res2_op_6v1_res0 = test.attr_op <0x2: builtin.int <si64>>:builtin.int <si64>;
                test.return res2_op_6v1_res0
            };
            test.return res0_op_3v1_res0
        }"#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}
