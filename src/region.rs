use crate::{
    basic_block::BasicBlock,
    context::{ArenaObj, Context, Ptr},
    linked_list::ContainsLinkedList,
    operation::Operation,
};

/// [BasicBlock]s contained in this [Region].
#[derive(Debug)]
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

/// An iterator for the [Operation]s in this [BasicBlock].
/// This is created by [Region::iter()].
pub struct Iter<'a> {
    next: Option<Ptr<BasicBlock>>,
    next_back: Option<Ptr<BasicBlock>>,
    ctx: &'a Context,
}

impl<'a> Iterator for Iter<'a> {
    type Item = Ptr<BasicBlock>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|curr| {
            if curr
                == self
                    .next_back
                    .expect("Some(next) => Some(next_back) violated")
            {
                self.next = None;
                self.next_back = None;
            } else {
                self.next = curr.deref(self.ctx).region_links.next_block;
            }
            curr
        })
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next_back.map(|curr| {
            if curr == self.next.expect("Some(next_back) => Some(next) violated") {
                self.next_back = None;
                self.next = None;
            } else {
                self.next_back = curr.deref(self.ctx).region_links.prev_block;
            }
            curr
        })
    }
}

/// A region is an ordered list of basic blocks contained in an Operation.
/// The first block, called the entry block is special. Its arguments
/// are considered to be the arguments to the region. It cannot have any
/// CFG predecessors (i.e., no block can branch to the entry block).
/// See [MLIR Region description](https://mlir.llvm.org/docs/LangRef/#regions).
#[derive(Debug)]
pub struct Region {
    pub(crate) self_ptr: Ptr<Region>,
    pub(crate) blocks_list: BlocksInRegion,
    pub(crate) parent_op: Ptr<Operation>,
}

impl Region {
    /// Get an iterator to the blocks inside this region.
    pub fn iter<'a>(&self, ctx: &'a Context) -> Iter<'a> {
        Iter {
            next: self.blocks_list.first,
            next_back: self.blocks_list.last,
            ctx,
        }
    }

    /// Create a new Region.
    pub fn new(ctx: &mut Context, parent_op: Ptr<Operation>) -> Ptr<Region> {
        let f = |self_ptr: Ptr<Region>| Region {
            self_ptr,
            blocks_list: BlocksInRegion::new_empty(),
            parent_op,
        };
        Self::alloc(ctx, f)
    }

    pub fn get_parent_op(&self) -> Ptr<Operation> {
        self.parent_op
    }
}

impl ContainsLinkedList<BasicBlock> for Region {
    fn get_head(&self) -> Option<Ptr<BasicBlock>> {
        self.blocks_list.first
    }

    fn get_tail(&self) -> Option<Ptr<BasicBlock>> {
        self.blocks_list.last
    }

    fn set_head(&mut self, head: Option<Ptr<BasicBlock>>) {
        self.blocks_list.first = head;
    }

    fn set_tail(&mut self, tail: Option<Ptr<BasicBlock>>) {
        self.blocks_list.last = tail;
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

    fn remove_references(_ptr: Ptr<Self>, _ctx: &mut Context) {
        todo!()
    }
}
