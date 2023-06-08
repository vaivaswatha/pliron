use crate::context::Context;
use crate::context::Ptr;
use crate::linked_list::ContainsLinkedList;

use super::Operation;

/// A utility result that is used to signal how to proceed with an ongoing walk:
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum WalkResut {
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
    pub fn walk<F>(&self, ctx: &Context, order: WalkOrder, callback: &mut F) -> WalkResut
    where
        F: FnMut(Ptr<Operation>) -> WalkResut,
    {
        if order == WalkOrder::PreOrder {
            match callback(*self) {
                WalkResut::Interrupt => return WalkResut::Interrupt,
                WalkResut::Skip => return WalkResut::Advance,
                WalkResut::Advance => (),
            }
        }
        let regions = self.deref(ctx).regions.clone();
        for region in regions {
            let blocks: Vec<_> = region.deref(ctx).iter(ctx).collect();
            for block in blocks {
                let block_ops: Vec<_> = block.deref_mut(ctx).iter(ctx).collect();
                for nested_op in block_ops {
                    if nested_op.walk(ctx, order, callback) == WalkResut::Interrupt {
                        return WalkResut::Interrupt;
                    }
                }
            }
        }
        if order == WalkOrder::PostOrder {
            return callback(*self);
        }
        WalkResut::Advance
    }
}
