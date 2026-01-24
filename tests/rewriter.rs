use crate::common::const_ret_in_mod;
use common::ConstantOp;
use expect_test::expect;
use pliron::{
    builtin::attributes::IntegerAttr,
    common_traits::Verify,
    context::{Context, Ptr},
    inserter::Inserter,
    op::Op,
    operation::Operation,
    printable::Printable,
    result::Result,
    rewriter::{IRRewriter, MatchRewrite, Rewriter, collect_rewrite},
};

#[cfg(target_family = "wasm")]
use wasm_bindgen_test::*;

mod common;

// Testing replacing all uses of c0 with c1.
#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn replace_c0_with_c1() -> Result<()> {
    let ctx = &mut Context::new();

    // const_ret_in_mod builds a module with a function.
    let (module_op, _, _const_op, _) = const_ret_in_mod(ctx).unwrap();

    struct ReplaceC0WithC1;

    impl MatchRewrite for ReplaceC0WithC1 {
        fn r#match(&mut self, ctx: &Context, op: Ptr<Operation>) -> bool {
            if let Some(const_op) = Operation::get_op::<ConstantOp>(op, ctx) {
                let val = const_op.get_value(ctx);
                return val
                    .downcast_ref::<IntegerAttr>()
                    .is_some_and(|int_attr| int_attr.get_value().to_u64() == 0);
            }
            false
        }

        fn rewrite(
            &mut self,
            ctx: &mut Context,
            rewriter: &mut IRRewriter,
            op: Ptr<Operation>,
        ) -> Result<()> {
            let const1_op = ConstantOp::new(ctx, 1).get_operation();
            rewriter.insert_operation(ctx, const1_op);
            rewriter.replace_operation(ctx, op, const1_op);
            Ok(())
        }
    }

    let rewriter = IRRewriter::default();
    collect_rewrite(ctx, ReplaceC0WithC1, rewriter, module_op.get_operation())?;

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                op5v1_res0 = test.constant builtin.integer <1: si64>;
                test.return op5v1_res0
            }
        }"#]]
    .assert_eq(&printed);

    module_op.get_operation().verify(ctx)?;

    Ok(())
}
