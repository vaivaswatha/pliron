use crate::context::Context;
use crate::context::Ptr;
use crate::linked_list::ContainsLinkedList;
use crate::op::Op;

use super::Operation;

/// A utility result that is used to signal how to proceed with an ongoing walk:
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum WalkResult {
    /// the walk will be interrupted and no more operations, regions
    /// or blocks will be visited.
    Interrupt,
    /// the walk will continue.
    Advance,
    /// the walk of the current operation, region or block and their
    /// nested elements that haven't been visited already will be skipped and will
    /// continue with the next operation, region or block.
    Skip,
}

/// Traversal order for region, block and operation walk utilities.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum WalkOrder {
    PreOrder,
    PostOrder,
}

impl Ptr<Operation> {
    /// Walk all of the regions, blocks for operations nested under (and including)
    /// the given operation. The walk order for enclosing regions, blocks and
    /// operations with respect to their nested ones
    /// is specified by 'order'. A callback on a block or operation is allowed to erase that block
    /// or operation only if the walk is in post-order.
    pub fn walk(
        &self,
        ctx: &Context,
        order: WalkOrder,
        callback: &mut impl FnMut(Ptr<Operation>) -> WalkResult,
    ) -> WalkResult {
        if order == WalkOrder::PreOrder {
            match callback(*self) {
                WalkResult::Interrupt => return WalkResult::Interrupt,
                WalkResult::Skip => return WalkResult::Advance,
                WalkResult::Advance => (),
            }
        }
        let regions = self.deref(ctx).regions.clone();
        for region in regions {
            let blocks: Vec<_> = region.deref(ctx).iter(ctx).collect();
            for block in blocks {
                let block_ops: Vec<_> = block.deref_mut(ctx).iter(ctx).collect();
                for nested_op in block_ops {
                    if nested_op.walk(ctx, order, callback) == WalkResult::Interrupt {
                        return WalkResult::Interrupt;
                    }
                }
            }
        }
        if order == WalkOrder::PostOrder {
            return callback(*self);
        }
        WalkResult::Advance
    }

    /// Walk all of the regions, blocks for specific operation type nested under (and including)
    /// the given operation. The walk order for enclosing regions, blocks and
    /// operations with respect to their nested ones
    /// is specified by 'order'. A callback on a block or operation is allowed to erase that block
    /// or operation only if the walk is in post-order.
    pub fn walk_only<T>(
        &self,
        ctx: &Context,
        order: WalkOrder,
        callback: &mut impl FnMut(&T) -> WalkResult,
    ) -> WalkResult
    where
        T: Op,
    {
        let self_deref = self.deref(ctx);
        let self_deref_op = self_deref.get_op(ctx);
        if order == WalkOrder::PreOrder {
            if let Some(t_op) = self_deref_op.downcast_ref::<T>() {
                match callback(t_op) {
                    WalkResult::Interrupt => return WalkResult::Interrupt,
                    WalkResult::Skip => return WalkResult::Advance,
                    WalkResult::Advance => (),
                }
            };
        }
        let regions = self_deref.regions.clone();
        for region in regions {
            let blocks: Vec<_> = region.deref(ctx).iter(ctx).collect();
            for block in blocks {
                let block_ops: Vec<_> = block.deref_mut(ctx).iter(ctx).collect();
                for nested_op in block_ops {
                    if nested_op.walk_only(ctx, order, callback) == WalkResult::Interrupt {
                        return WalkResult::Interrupt;
                    }
                }
            }
        }
        if order == WalkOrder::PostOrder {
            if let Some(t_op) = self_deref_op.downcast_ref::<T>() {
                return callback(t_op);
            };
        }
        WalkResult::Advance
    }
}

#[cfg(test)]
mod tests {
    use apint::ApInt;

    use crate::common_traits::Verify;
    use crate::debug_info::set_operation_result_name;
    use crate::dialects;
    use crate::dialects::builtin::attributes::IntegerAttr;
    use crate::dialects::builtin::op_interfaces::OneResultInterface;
    use crate::dialects::builtin::ops::ConstantOp;
    use crate::dialects::builtin::ops::FuncOp;
    use crate::dialects::builtin::ops::ModuleOp;
    use crate::dialects::builtin::types::FunctionType;
    use crate::dialects::builtin::types::IntegerType;
    use crate::dialects::builtin::types::Signedness;
    use crate::dialects::llvm::ops::ReturnOp;
    use crate::error::CompilerError;
    use crate::with_context::AttachContext;

    use super::*;

    // Create a print a module "bar", with a function "foo"
    // containing a single `return 0`.
    fn create_mod_op(ctx: &mut Context) -> Result<ModuleOp, CompilerError> {
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

    fn setup_context_dialects() -> Context {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);
        dialects::llvm::register(&mut ctx);
        ctx
    }

    #[test]
    fn smoke_walk_only() {
        let mut ctx = setup_context_dialects();
        let module_op = create_mod_op(&mut ctx).unwrap();
        let mut return_ops = vec![];
        module_op.get_operation().walk_only::<ReturnOp>(
            &ctx,
            WalkOrder::PreOrder,
            &mut |return_op| {
                return_ops.push(return_op.get_operation());
                WalkResult::Advance
            },
        );
        let _ = return_ops
            .first()
            .unwrap()
            .deref(&ctx)
            .get_op(&ctx)
            .downcast_ref::<ReturnOp>()
            .unwrap();
        assert_eq!(return_ops.len(), 1);
    }
}
