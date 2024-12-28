//! Test format derive for `Op`s.

use expect_test::expect;
use pliron::{
    builtin::op_interfaces::{
        OneOpdInterface, OneResultInterface, ZeroOpdInterface, ZeroResultInterface,
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
        builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry_block_1v1():
            res0_op_2v1_res0 = test.one_result_zero_operands :builtin.int <si64>;
            test.return res0_op_2v1_res0
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
        builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry_block_1v1():
            res0_op_2v1_res0 = test.one_result_zero_operands :builtin.int <si64>;
            res1_op_3v1_res0 = test.one_result_one_operand res0_op_2v1_res0:builtin.int <si64>;
            test.return res1_op_3v1_res0
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
        builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry_block_1v1():
            res0_op_2v1_res0 = test.one_result_zero_operands :builtin.int <si64>;
            res1a_op_3v1_res0, res1b_op_3v1_res1 = test.two_results_two_operands res0_op_2v1_res0,res0_op_2v1_res0:(builtin.int <si64>,builtin.int <si64>);
            test.return res1a_op_3v1_res0
        }"#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}
