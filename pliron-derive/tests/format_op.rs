//! Test format derive for `Op`s.

use combine::Parser;
use expect_test::expect;
use pliron::{
    builtin::op_interfaces::{
        IsTerminatorInterface, IsolatedFromAboveInterface, OneOpdInterface, OneRegionInterface,
        OneResultInterface, ZeroOpdInterface, ZeroResultInterface,
    },
    common_traits::Verify,
    impl_verify_succ, location,
    op::Op,
    operation::Operation,
    parsable::{self, Parsable, state_stream_from_iterator},
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
    expect![r#"test.zero_results_zero_operands "#].assert_eq(&printed);

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("ZeroResultsZeroOperands parser failed");
    expect![[r#"
        test.zero_results_zero_operands  !0

        outlined_attributes:
        !0 = @[<in-memory>: line: 1, column: 1], []
    "#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[format_op("`: ` type($0)")]
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
            res0 = test.one_result_zero_operands : builtin.integer si64;
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("OneResultZeroOperands parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block1v1():
            res0_op2v1_res0 = test.one_result_zero_operands : builtin.integer si64 !0;
            test.return res0_op2v1_res0 !1
        } !2

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 4, column: 13], []
        !2 = @[<in-memory>: line: 1, column: 1], []
    "#]]
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
            res0 = test.one_result_zero_operands : builtin.integer si64;
            res1 = test.one_result_one_operand res0 : builtin.integer si64;
            test.return res1
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("OneResultOneOperand parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block1v1():
            res0_op2v1_res0 = test.one_result_zero_operands : builtin.integer si64 !0;
            res1_op3v1_res0 = test.one_result_one_operand res0_op2v1_res0:builtin.integer si64 !1;
            test.return res1_op3v1_res0 !2
        } !3

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 4, column: 13], []
        !2 = @[<in-memory>: line: 5, column: 13], []
        !3 = @[<in-memory>: line: 1, column: 1], []
    "#]]
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
            res0 = test.one_result_zero_operands :builtin.integer si64;
            res1a, res1b = test.two_results_two_operands res0, res0 : (builtin.integer si64, builtin.integer si64);
            test.return res1a
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("TwoResultTwoOperands parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block1v1():
            res0_op2v1_res0 = test.one_result_zero_operands : builtin.integer si64 !0;
            res1a_op3v1_res0, res1b_op3v1_res1 = test.two_results_two_operands res0_op2v1_res0,res0_op2v1_res0:(builtin.integer si64,builtin.integer si64) !1;
            test.return res1a_op3v1_res0 !2
        } !3

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 4, column: 13], []
        !2 = @[<in-memory>: line: 5, column: 13], []
        !3 = @[<in-memory>: line: 1, column: 1], []
    "#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[format_op("$0 `: ` `(` types(CharSpace(`,`)) `)`")]
#[def_op("test.two_results_one_operand")]
struct TwoResultsOneOperandOp {}
impl_verify_succ!(TwoResultsOneOperandOp);

#[test]
fn two_results_one_operand() {
    let ctx = &mut setup_context_dialects();
    OneResultZeroOperandsOp::register(ctx, OneResultZeroOperandsOp::parser_fn);
    TwoResultsOneOperandOp::register(ctx, TwoResultsOneOperandOp::parser_fn);

    let printed = "builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry():
            res0 = test.one_result_zero_operands : builtin.integer si64;
            res1a, res1b = test.two_results_one_operand res0 : (builtin.integer si64, builtin.integer si64);
            test.return res1a
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("TwoResultsOneOperand parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block1v1():
            res0_op2v1_res0 = test.one_result_zero_operands : builtin.integer si64 !0;
            res1a_op3v1_res0, res1b_op3v1_res1 = test.two_results_one_operand res0_op2v1_res0: (builtin.integer si64, builtin.integer si64) !1;
            test.return res1a_op3v1_res0 !2
        } !3

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 4, column: 13], []
        !2 = @[<in-memory>: line: 5, column: 13], []
        !3 = @[<in-memory>: line: 1, column: 1], []
    "#]]
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
            res0 = test.attr_op <0: si64> :builtin.integer si64;
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("AttrOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block1v1():
            res0_op2v1_res0 = test.attr_op <0: si64>:builtin.integer si64 !0;
            test.return res0_op2v1_res0 !1
        } !2

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 4, column: 13], []
        !2 = @[<in-memory>: line: 1, column: 1], []
    "#]]
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
            res0 = test.attr_op2 \"Hello World\" :builtin.integer si64;
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("AttrOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block1v1():
            res0_op2v1_res0 = test.attr_op2 "Hello World":builtin.integer si64 !0;
            test.return res0_op2v1_res0 !1
        } !2

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 4, column: 13], []
        !2 = @[<in-memory>: line: 1, column: 1], []
    "#]]
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
            res0 = test.attr_op3 builtin.integer <0: si64> :builtin.integer si64;
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("AttrOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block1v1():
            res0_op2v1_res0 = test.attr_op3 builtin.integer <0: si64>:builtin.integer si64 !0;
            test.return res0_op2v1_res0 !1
        } !2

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 4, column: 13], []
        !2 = @[<in-memory>: line: 1, column: 1], []
    "#]]
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
            res0 = test.attr_op <0: si64> :builtin.integer si64;
            test.if_op (res0) {
              ^then():
                res1 = test.attr_op <1: si64> :builtin.integer si64;
                test.return res1
            };
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("IfOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block2v1():
            res0_op2v1_res0 = test.attr_op <0: si64>:builtin.integer si64 !0;
            test.if_op (res0_op2v1_res0)
            {
              ^then_block1v1():
                res1_op4v1_res0 = test.attr_op <1: si64>:builtin.integer si64 !1;
                test.return res1_op4v1_res0 !2
            } !3;
            test.return res0_op2v1_res0 !4
        } !5

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 6, column: 17], []
        !2 = @[<in-memory>: line: 7, column: 17], []
        !3 = @[<in-memory>: line: 4, column: 13], []
        !4 = @[<in-memory>: line: 9, column: 13], []
        !5 = @[<in-memory>: line: 1, column: 1], []
    "#]]
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
            res0 = test.attr_op <0: si64> :builtin.integer si64;
            test.if_else_op (res0) {
              ^then():
                res1 = test.attr_op <1: si64> :builtin.integer si64;
                test.return res1
            } else {
              ^else():
                res2 = test.attr_op <2: si64> :builtin.integer si64;
                test.return res2
            };
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("IfOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block3v1():
            res0_op2v1_res0 = test.attr_op <0: si64>:builtin.integer si64 !0;
            test.if_else_op (res0_op2v1_res0)
            {
              ^then_block1v1():
                res1_op4v1_res0 = test.attr_op <1: si64>:builtin.integer si64 !1;
                test.return res1_op4v1_res0 !2
            }else
            {
              ^else_block2v1():
                res2_op6v1_res0 = test.attr_op <2: si64>:builtin.integer si64 !3;
                test.return res2_op6v1_res0 !4
            } !5;
            test.return res0_op2v1_res0 !6
        } !7

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 6, column: 17], []
        !2 = @[<in-memory>: line: 7, column: 17], []
        !3 = @[<in-memory>: line: 10, column: 17], []
        !4 = @[<in-memory>: line: 11, column: 17], []
        !5 = @[<in-memory>: line: 4, column: 13], []
        !6 = @[<in-memory>: line: 13, column: 13], []
        !7 = @[<in-memory>: line: 1, column: 1], []
    "#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[def_op("test.br")]
#[format_op("succ($0) `(` operands(CharSpace(`,`)) `)`")]
#[derive_op_interface_impl(IsTerminatorInterface)]
pub struct BrOp;
impl_verify_succ!(BrOp);

#[test]
fn br_op() {
    let ctx = &mut setup_context_dialects();
    AttrOp::register(ctx, AttrOp::parser_fn);
    BrOp::register(ctx, BrOp::parser_fn);

    let printed = "builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry():
            res0 = test.attr_op <0: si64> :builtin.integer si64;
            test.br ^bb1(res0)
          ^bb1(arg0 : builtin.integer si64):
            test.return arg0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("BrOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block2v1():
            res0_op2v1_res0 = test.attr_op <0: si64>:builtin.integer si64 !0;
            test.br ^bb1_block3v1(res0_op2v1_res0) !1

          ^bb1_block3v1(arg0_block3v1_arg0: builtin.integer si64):
            test.return arg0_block3v1_arg0 !2
        } !3

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 4, column: 13], []
        !2 = @[<in-memory>: line: 6, column: 13], []
        !3 = @[<in-memory>: line: 1, column: 1], []
    "#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[def_op("test.multiple_successors")]
#[format_op("`[` successors(CharSpace(`,`)) `]`")]
#[derive_op_interface_impl(IsTerminatorInterface)]
pub struct MultipleSuccessorsOp;
impl_verify_succ!(MultipleSuccessorsOp);

#[test]
fn multiple_successors_op() {
    let ctx = &mut setup_context_dialects();
    AttrOp::register(ctx, AttrOp::parser_fn);
    MultipleSuccessorsOp::register(ctx, MultipleSuccessorsOp::parser_fn);

    let printed = "builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry():
            res0 = test.attr_op <0: si64> :builtin.integer si64;
            test.multiple_successors [^bb1, ^bb2]
          ^bb1():
            test.return res0
          ^bb2():
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("MultipleSuccessorsOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block3v1():
            res0_op2v1_res0 = test.attr_op <0: si64>:builtin.integer si64 !0;
            test.multiple_successors [^bb1_block4v1, ^bb2_block1v3] !1

          ^bb1_block4v1():
            test.return res0_op2v1_res0 !2

          ^bb2_block1v3():
            test.return res0_op2v1_res0 !3
        } !4

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 4, column: 13], []
        !2 = @[<in-memory>: line: 6, column: 13], []
        !3 = @[<in-memory>: line: 8, column: 13], []
        !4 = @[<in-memory>: line: 1, column: 1], []
    "#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[def_op("test.multiple_regions")]
#[format_op("`[` regions(CharSpace(`,`)) `]`")]
pub struct MultipleRegionsOp;
impl_verify_succ!(MultipleRegionsOp);

#[test]
fn multiple_regions_op() {
    let ctx = &mut setup_context_dialects();
    AttrOp::register(ctx, AttrOp::parser_fn);
    MultipleRegionsOp::register(ctx, MultipleRegionsOp::parser_fn);

    let printed = "
    builtin.func @testfunc: builtin.function <()->()> {
      ^entry():
        res = test.attr_op <0: si64> :builtin.integer si64;
        test.multiple_regions [
            {
                ^reg1_entry():
                    res0 = test.attr_op <0: si64> :builtin.integer si64;
                    test.return res0
            }, {
                ^reg2_entry():
                    res1 = test.attr_op <1: si64> :builtin.integer si64;
                    test.return res1
            }
        ];
        test.return res
    }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("MultipleRegionsOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block3v1():
            res_op2v1_res0 = test.attr_op <0: si64>:builtin.integer si64 !0;
            test.multiple_regions [
            {
              ^reg1_entry_block1v1():
                res0_op4v1_res0 = test.attr_op <0: si64>:builtin.integer si64 !1;
                test.return res0_op4v1_res0 !2
            }, 
            {
              ^reg2_entry_block2v1():
                res1_op6v1_res0 = test.attr_op <1: si64>:builtin.integer si64 !3;
                test.return res1_op6v1_res0 !4
            }] !5;
            test.return res_op2v1_res0 !6
        } !7

        outlined_attributes:
        !0 = @[<in-memory>: line: 4, column: 9], []
        !1 = @[<in-memory>: line: 8, column: 21], []
        !2 = @[<in-memory>: line: 9, column: 21], []
        !3 = @[<in-memory>: line: 12, column: 21], []
        !4 = @[<in-memory>: line: 13, column: 21], []
        !5 = @[<in-memory>: line: 5, column: 9], []
        !6 = @[<in-memory>: line: 16, column: 9], []
        !7 = @[<in-memory>: line: 1, column: 1], []
    "#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[def_op("test.attr_dict")]
#[format_op("attr_dict")]
struct AttrDictOp;
impl_verify_succ!(AttrDictOp);

#[test]
fn attr_dict_op() {
    let ctx = &mut setup_context_dialects();
    AttrDictOp::register(ctx, AttrDictOp::parser_fn);
    AttrOp::register(ctx, AttrOp::parser_fn);

    let printed = "builtin.func @testfunc: builtin.function <() -> ()> {
          ^entry():
            res0 = test.attr_op <3: si64> :builtin.integer si64;
            test.attr_dict [
                (attr1: builtin.integer <0: si64>),
                (attr2: builtin.integer <1: si64>)
            ];
            test.return res0
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("AttrDictOp parser failed");

    expect![[r#"
        builtin.func @testfunc: builtin.function <()->()> 
        {
          ^entry_block1v1():
            res0_op2v1_res0 = test.attr_op <3: si64>:builtin.integer si64 !0;
            test.attr_dict [(attr1: builtin.integer <0: si64>), (attr2: builtin.integer <1: si64>)] !1;
            test.return res0_op2v1_res0 !2
        } !3

        outlined_attributes:
        !0 = @[<in-memory>: line: 3, column: 13], []
        !1 = @[<in-memory>: line: 4, column: 13], []
        !2 = @[<in-memory>: line: 8, column: 13], []
        !3 = @[<in-memory>: line: 1, column: 1], []
    "#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());
}

#[def_op("test.multiple_regions2")]
#[format_op]
pub struct MultipleRegions2Op;
impl_verify_succ!(MultipleRegions2Op);

#[test]
fn multiple_regions2_op() {
    let ctx = &mut setup_context_dialects();
    AttrOp::register(ctx, AttrOp::parser_fn);
    MultipleRegions2Op::register(ctx, MultipleRegions2Op::parser_fn);

    let printed = "
        test.multiple_regions2 () [] [] : <()->()>
        {
            ^reg1_entry():
                res0 = test.attr_op <0: si64> :builtin.integer si64;
                test.return res0
        }, {
            ^reg2_entry():
                res1 = test.attr_op <1: si64> :builtin.integer si64;
                test.return res1
        }";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let actual = Operation::top_level_parser()
        .parse(state_stream)
        .err()
        .unwrap();
    let expected_err = expect![[r#"
        Parse error at line: 1, column: 1
        Regions in a top-level operation must be IsolatedFromAbove
    "#]];
    expected_err.assert_eq(&actual.to_string());
}

#[def_op("test.multiple_regions3")]
#[format_op("`[` regions(CharSpace(`,`)) `]`")]
pub struct MultipleRegions3Op;
impl_verify_succ!(MultipleRegions3Op);

#[test]
fn multiple_regions3_op() {
    let ctx = &mut setup_context_dialects();
    AttrOp::register(ctx, AttrOp::parser_fn);
    MultipleRegions3Op::register(ctx, MultipleRegions3Op::parser_fn);

    let printed = "
        test.multiple_regions3 [
            {
                ^reg1_entry():
                    res0 = test.attr_op <0: si64> :builtin.integer si64;
                    test.return res0
            }, {
                ^reg2_entry():
                    res1 = test.attr_op <1: si64> :builtin.integer si64;
                    test.return res1
            }
        ]";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );

    let actual = Operation::top_level_parser()
        .parse(state_stream)
        .err()
        .unwrap();
    let expected_err = expect![[r#"
        Parse error at line: 1, column: 1
        Regions in a top-level operation must be IsolatedFromAbove
    "#]];
    expected_err.assert_eq(&actual.to_string());
}

#[def_op("test.multiple_regions4")]
#[format_op("`[` regions(CharSpace(`,`)) `]`")]
#[derive_op_interface_impl(IsolatedFromAboveInterface)]
pub struct MultipleRegions4Op;
impl_verify_succ!(MultipleRegions4Op);

#[test]
fn multiple_regions4_op() {
    let ctx = &mut setup_context_dialects();
    AttrOp::register(ctx, AttrOp::parser_fn);
    MultipleRegions4Op::register(ctx, MultipleRegions4Op::parser_fn);

    let printed = "
        test.multiple_regions4 [
            {
                ^reg1_entry():
                    res0 = test.attr_op <0: si64> :builtin.integer si64;
                    test.return res0
            }, {
                ^reg2_entry():
                    res1 = test.attr_op <1: si64> :builtin.integer si64;
                    test.return res1
            }
        ]";

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let (res, _) = Operation::top_level_parser()
        .parse(state_stream)
        .expect("MultipleRegions4 parser failed");

    expect![[r#"
        test.multiple_regions4 [
        {
          ^reg1_entry_block1v1():
            res0_op2v1_res0 = test.attr_op <0: si64>:builtin.integer si64 !0;
            test.return res0_op2v1_res0 !1
        }, 
        {
          ^reg2_entry_block2v1():
            res1_op4v1_res0 = test.attr_op <1: si64>:builtin.integer si64 !2;
            test.return res1_op4v1_res0 !3
        }] !4

        outlined_attributes:
        !0 = @[<in-memory>: line: 5, column: 21], []
        !1 = @[<in-memory>: line: 6, column: 21], []
        !2 = @[<in-memory>: line: 9, column: 21], []
        !3 = @[<in-memory>: line: 10, column: 21], []
        !4 = @[<in-memory>: line: 1, column: 1], []
    "#]]
    .assert_eq(&res.disp(ctx).to_string());

    assert!(res.verify(ctx).is_ok());

    Operation::erase(res, ctx);
    assert!(ctx.operations.is_empty());
    assert!(ctx.regions.is_empty());
    assert!(ctx.basic_blocks.is_empty());
}
