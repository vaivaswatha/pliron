//! Utility functions for various graph traversals

/// Region traversal utilities
pub mod region {
    use rustc_hash::FxHashSet;

    use crate::{
        basic_block::BasicBlock,
        context::{Context, Ptr},
        linked_list::ContainsLinkedList,
        region::Region,
    };

    /// Compute post-order of the blocks in a region.
    pub fn post_order(ctx: &Context, reg: Ptr<Region>) -> Vec<Ptr<BasicBlock>> {
        let on_stack = &mut FxHashSet::<Ptr<BasicBlock>>::default();
        let mut po = Vec::<Ptr<BasicBlock>>::new();

        fn walk(
            ctx: &Context,
            block: Ptr<BasicBlock>,
            on_stack: &mut FxHashSet<Ptr<BasicBlock>>,
            po: &mut Vec<Ptr<BasicBlock>>,
        ) {
            if !on_stack.insert(block) {
                // block already visited.
                return;
            }
            // Visit successors before visiting self.
            for succ in block.deref(ctx).succs(ctx) {
                walk(ctx, succ, on_stack, po);
            }
            // Visit self.
            po.push(block);
        }

        // Walk every block (not just entry) since we may have unreachable blocks.
        for block in reg.deref(ctx).iter(ctx) {
            walk(ctx, block, on_stack, &mut po);
        }

        po
    }

    /// Compute reverse-post-order of the blocks in a region.
    pub fn topological_order(ctx: &Context, reg: Ptr<Region>) -> Vec<Ptr<BasicBlock>> {
        let mut po = post_order(ctx, reg);
        po.reverse();
        po
    }
}
