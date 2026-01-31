use core::panic;

use crate::common::const_ret_in_mod;
use common::ConstantOp;
use expect_test::expect;
use pliron::{
    builtin::{
        attributes::IntegerAttr,
        op_interfaces::{
            IsolatedFromAboveInterface, NOpdsInterface, NResultsInterface, OneOpdInterface,
            OneResultInterface, SingleBlockRegionInterface, SymbolOpInterface,
        },
        types::{IntegerType, Signedness},
    },
    common_traits::Verify,
    context::{Context, Ptr},
    identifier::Identifier,
    impl_verify_succ,
    irbuild::{
        inserter::{Inserter, OpInsertionPoint},
        match_rewrite::{MatchRewrite, MatchRewriter, collect_rewrite},
        rewriter::{Rewriter, ScopedRewriter},
    },
    op::Op,
    operation::Operation,
    printable::Printable,
    result::Result,
    r#type::TypeObj,
    value::Value,
};

use pliron_derive::{
    def_op, def_type, derive_attr_get_set, derive_op_interface_impl, derive_type_get, format_op,
    format_type,
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
    let (module_op, _, const_op, _) = const_ret_in_mod(ctx).unwrap();
    assert!(
        const_op
            .get_value(ctx)
            .downcast_ref::<IntegerAttr>()
            .unwrap()
            .value()
            .to_u64()
            == 0
    );

    struct ReplaceC0WithC1;

    impl MatchRewrite for ReplaceC0WithC1 {
        fn r#match(&mut self, ctx: &Context, op: Ptr<Operation>) -> bool {
            if let Some(const_op) = Operation::get_op::<ConstantOp>(op, ctx) {
                let val = const_op.get_value(ctx);
                return val
                    .downcast_ref::<IntegerAttr>()
                    .is_some_and(|int_attr| int_attr.value().to_u64() < 2);
            }
            false
        }

        fn rewrite(
            &mut self,
            ctx: &mut Context,
            rewriter: &mut MatchRewriter,
            op: Ptr<Operation>,
        ) -> Result<()> {
            let Some(const_op) =
                Operation::get_op::<ConstantOp>(op, ctx).map(|co| co.get_value(ctx))
            else {
                panic!("Expected ConstantOp");
            };
            let cur_val = const_op
                .downcast_ref::<IntegerAttr>()
                .unwrap()
                .value()
                .to_u64();
            if cur_val >= 2 {
                panic!("Expected match only on constant value less than 2");
            }
            let const1_op = ConstantOp::new(ctx, cur_val + 1).get_operation();
            rewriter.insert_operation(ctx, const1_op);
            rewriter.replace_operation(ctx, op, const1_op);
            Ok(())
        }
    }

    // Collect and rewrite must replace constant 0 with constant 1,
    // and then constant 1 with constant 2.
    collect_rewrite(ctx, ReplaceC0WithC1, module_op.get_operation())?;
    module_op.get_operation().verify(ctx)?;

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                op3v3_res0 = test.constant builtin.integer <2: si64>;
                test.return op3v3_res0
            }
        }"#]]
    .assert_eq(&printed);

    Ok(())
}

/// A test global operation.
#[def_op("test.global")]
#[format_op]
#[derive_op_interface_impl(
    IsolatedFromAboveInterface,
    NOpdsInterface<0>,
    NResultsInterface<1>,
    OneResultInterface,
    SymbolOpInterface,
    SingleBlockRegionInterface,
)]
#[derive_attr_get_set(test_global_op_const_val: IntegerAttr)]
pub struct GlobalOp;
impl_verify_succ!(GlobalOp);

impl GlobalOp {
    /// Create a new [GlobalOp].
    pub fn new(ctx: &mut Context, name: Identifier, val: IntegerAttr) -> Self {
        let op = Operation::new(
            ctx,
            Self::get_concrete_op_info(),
            vec![PointerType::get(ctx).into()],
            vec![],
            vec![],
            0,
        );
        let op = GlobalOp { op };
        op.set_symbol_name(ctx, name);
        op.set_attr_test_global_op_const_val(ctx, val);
        op
    }
}

/// An opaque pointer
#[def_type("test.ptr")]
#[derive_type_get]
#[derive(Hash, PartialEq, Eq, Debug)]
#[format_type]
pub struct PointerType;
impl_verify_succ!(PointerType);

#[def_op("test.load")]
#[format_op("$0 ` ` : ` type($0)")]
#[derive_op_interface_impl(OneResultInterface, OneOpdInterface, NResultsInterface<1>, NOpdsInterface<1>)]
pub struct LoadOp;
impl_verify_succ!(LoadOp);

impl LoadOp {
    /// Create a new [LoadOp]
    pub fn new(ctx: &mut Context, ptr: Value, res_ty: Ptr<TypeObj>) -> Self {
        LoadOp {
            op: Operation::new(
                ctx,
                Self::get_concrete_op_info(),
                vec![res_ty],
                vec![ptr],
                vec![],
                0,
            ),
        }
    }
}

/// Test scoped rewriter that sets the insertion point for the duration of its lifetime.
#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn scoped_rewriter_test() -> Result<()> {
    let ctx = &mut Context::new();
    let (module_op, _func_op, _, _) = const_ret_in_mod(ctx).unwrap();

    // For each constant operation, create a global in the parent module and load from that.
    struct ConstToGlobal;
    impl MatchRewrite for ConstToGlobal {
        fn r#match(&mut self, ctx: &Context, op: Ptr<Operation>) -> bool {
            Operation::get_op::<ConstantOp>(op, ctx).is_some()
        }

        fn rewrite(
            &mut self,
            ctx: &mut Context,
            rewriter: &mut MatchRewriter,
            op: Ptr<Operation>,
        ) -> Result<()> {
            let const_op = Operation::get_op::<ConstantOp>(op, ctx).unwrap();
            let val = const_op.get_value(ctx).downcast::<IntegerAttr>().unwrap();

            // Create a global in the module.
            let func_op = op.deref(ctx).get_parent_op(ctx).unwrap();
            let module_op = func_op.deref(ctx).get_parent_op(ctx).unwrap();
            let module_op =
                Operation::get_op::<pliron::builtin::ops::ModuleOp>(module_op, ctx).unwrap();

            let name =
                Identifier::try_from("global_".to_string() + &val.value().to_string(10, true))
                    .unwrap();
            let global_op = GlobalOp::new(ctx, name, *val);
            {
                let mut module_inserter = ScopedRewriter::new(
                    rewriter,
                    OpInsertionPoint::AtBlockStart(module_op.get_body(ctx, 0)),
                );
                module_inserter.insert_operation(ctx, global_op.get_operation());
            }

            let int_ty = IntegerType::get(ctx, 32, Signedness::Signed).into();
            let load_op = LoadOp::new(ctx, global_op.get_result(ctx), int_ty).get_operation();
            rewriter.insert_operation(ctx, load_op);

            // Replace uses of the constant with the load.
            rewriter.replace_operation(ctx, op, load_op);
            Ok(())
        }
    }

    collect_rewrite(ctx, ConstToGlobal, module_op.get_operation())?;
    module_op.get_operation().verify(ctx)?;

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            op5v1_res0 = test.global () [] [test_global_op_const_val: builtin.integer <0: si64>, sym_name: builtin.identifier global_0]: <() -> (test.ptr )>;
            builtin.func @foo: builtin.function <()->(builtin.integer si64)> 
            {
              ^entry_block2v1():
                op6v1_res0 = test.load op5v1_res0 ;
                test.return op6v1_res0
            }
        }"#]].assert_eq(&printed);

    Ok(())
}

/// Test that erases a function containing a constant 0 operation.
#[test]
#[cfg_attr(target_family = "wasm", wasm_bindgen_test)]
fn erase_func_with_const_zero() -> Result<()> {
    let ctx = &mut Context::new();
    let (module_op, _func_op, _, _) = const_ret_in_mod(ctx).unwrap();

    struct EraseFunc;
    impl MatchRewrite for EraseFunc {
        fn r#match(&mut self, ctx: &Context, op: Ptr<Operation>) -> bool {
            if let Some(const_op) = Operation::get_op::<ConstantOp>(op, ctx) {
                let val = const_op.get_value(ctx);
                return val
                    .downcast_ref::<IntegerAttr>()
                    .is_some_and(|int_attr| int_attr.value().to_u64() == 0);
            }
            false
        }

        fn rewrite(
            &mut self,
            ctx: &mut Context,
            rewriter: &mut MatchRewriter,
            op: Ptr<Operation>,
        ) -> Result<()> {
            // Insert a constant 1 operation before erasing the function.
            let const1_op = ConstantOp::new(ctx, 1).get_operation();
            rewriter.insert_operation(ctx, const1_op);
            // Insert a constant 0 operation before erasing the function.
            let const0_op = ConstantOp::new(ctx, 0).get_operation();
            rewriter.insert_operation(ctx, const0_op);

            let func_op = op.deref(ctx).get_parent_op(ctx).unwrap();
            rewriter.erase_operation(ctx, func_op);
            Ok(())
        }
    }

    collect_rewrite(ctx, EraseFunc, module_op.get_operation())?;
    module_op.get_operation().verify(ctx)?;

    let printed = format!("{}", module_op.disp(ctx));
    expect![[r#"
        builtin.module @bar 
        {
          ^block1v1():
            
        }"#]]
    .assert_eq(&printed);

    Ok(())
}
