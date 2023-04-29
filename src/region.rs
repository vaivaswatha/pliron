//! Regions are containers for [BasicBlock]s within an [Operation].
use crate::{
    basic_block::BasicBlock,
    common_traits::{DisplayWithContext, Verify},
    context::{private::ArenaObj, Context, Ptr},
    error::CompilerError,
    linked_list::{private, ContainsLinkedList},
    operation::Operation,
    with_context::AttachContext,
};

/// [BasicBlock]s contained in this [Region].
pub struct BlocksInRegion {
    first: Option<Ptr<BasicBlock>>,
    last: Option<Ptr<BasicBlock>>,
}

impl BlocksInRegion {
    fn new_empty() -> BlocksInRegion {
        BlocksInRegion {
            first: None,
            last: None,
        }
    }
}

/// A region is an ordered list of basic blocks contained in an Operation.
/// The first block, called the entry block is special. Its arguments
/// are considered to be the arguments to the region. It cannot have any
/// CFG predecessors (i.e., no block can branch to the entry block).
/// See [MLIR Region description](https://mlir.llvm.org/docs/LangRef/#regions).
pub struct Region {
    pub(crate) self_ptr: Ptr<Region>,
    pub(crate) blocks_list: BlocksInRegion,
    pub(crate) parent_op: Ptr<Operation>,
}

impl Region {
    /// Create a new Region.
    pub fn new(ctx: &mut Context, parent_op: Ptr<Operation>) -> Ptr<Region> {
        let f = |self_ptr: Ptr<Region>| Region {
            self_ptr,
            blocks_list: BlocksInRegion::new_empty(),
            parent_op,
        };
        Self::alloc(ctx, f)
    }

    /// Get the operation that contains this region.
    pub fn get_parent_op(&self) -> Ptr<Operation> {
        self.parent_op
    }

    /// Drop all uses that this region holds.
    pub fn drop_all_uses(ptr: Ptr<Self>, ctx: &mut Context) {
        let blocks: Vec<_> = ptr.deref(ctx).iter(ctx).collect();
        for block in blocks {
            BasicBlock::drop_all_uses(block, ctx);
        }
    }
}

impl private::ContainsLinkedList<BasicBlock> for Region {
    fn set_head(&mut self, head: Option<Ptr<BasicBlock>>) {
        self.blocks_list.first = head;
    }
    fn set_tail(&mut self, tail: Option<Ptr<BasicBlock>>) {
        self.blocks_list.last = tail;
    }
}

impl ContainsLinkedList<BasicBlock> for Region {
    fn get_head(&self) -> Option<Ptr<BasicBlock>> {
        self.blocks_list.first
    }
    fn get_tail(&self) -> Option<Ptr<BasicBlock>> {
        self.blocks_list.last
    }
}

impl ArenaObj for Region {
    fn get_arena(ctx: &Context) -> &crate::context::ArenaCell<Self> {
        &ctx.regions
    }

    fn get_arena_mut(ctx: &mut Context) -> &mut crate::context::ArenaCell<Self> {
        &mut ctx.regions
    }

    fn get_self_ptr(&self, _ctx: &Context) -> Ptr<Self> {
        self.self_ptr
    }

    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context) {
        let blocks: Vec<_> = ptr.deref_mut(ctx).iter(ctx).collect();
        for block in blocks {
            ArenaObj::dealloc(block, ctx);
        }
    }
}

impl Verify for Region {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
        self.iter(ctx).try_for_each(|op| op.deref(ctx).verify(ctx))
    }
}

impl AttachContext for Region {}
impl DisplayWithContext for Region {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for block in self.iter(ctx) {
            write!(f, "{}", block.with_ctx(ctx))?;
        }
        Ok(())
    }
}
