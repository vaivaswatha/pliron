use crate::{
    context::{ArenaCell, ArenaObj, Context, Ptr},
    linked_list::{ContainsLinkedList, LinkedList},
    operation::Operation,
    use_def_lists::{Def, DefDescr, Use, UseDescr},
    value::Value,
    vec_exns::VecExtns,
};

#[derive(Debug)]
pub struct BlockArgument {
    def: Def,
    def_block: Ptr<BasicBlock>,
    arg_idx: usize,
}

impl Value for BlockArgument {
    fn get_defining_op(&self) -> Option<Ptr<Operation>> {
        None
    }

    fn get_parent_block(&self, _ctx: &Context) -> Option<Ptr<BasicBlock>> {
        Some(self.def_block)
    }

    fn get_def_index(&self) -> usize {
        self.arg_idx
    }

    fn get_uses(&self) -> &Vec<UseDescr> {
        &self.def.uses
    }

    fn get_uses_mut(&mut self) -> &mut Vec<UseDescr> {
        &mut self.def.uses
    }

    fn add_use(&mut self, r#use: UseDescr) -> Use {
        let use_idx = self.def.uses.push_back(r#use);
        Use {
            def: DefDescr::BlockArgument {
                block: self.def_block,
                arg_idx: self.get_def_index(),
            },
            use_idx,
        }
    }
}

#[derive(Debug)]
pub struct OpsInBlock {
    first: Option<Ptr<Operation>>,
    last: Option<Ptr<Operation>>,
}

impl OpsInBlock {
    fn new_empty() -> OpsInBlock {
        OpsInBlock {
            first: None,
            last: None,
        }
    }
}

struct OpsInBlockIter<'a> {
    curr: Option<Ptr<Operation>>,
    ctx: &'a Context,
}

impl<'a> Iterator for OpsInBlockIter<'a> {
    type Item = Ptr<Operation>;

    fn next(&mut self) -> Option<Self::Item> {
        self.curr.map(|curr| {
            let next = curr.deref(&self.ctx).block_links.next_op;
            self.curr = next;
            curr
        })
    }
}

#[derive(Debug)]
pub struct BasicBlock {
    pub self_ptr: Ptr<BasicBlock>,
    pub ops_list: OpsInBlock,
    pub args: Vec<BlockArgument>,
}

impl BasicBlock {
    fn get_ops_iter<'a>(&self, ctx: &'a Context) -> OpsInBlockIter<'a> {
        OpsInBlockIter {
            curr: self.ops_list.first,
            ctx,
        }
    }
    pub fn new(ctx: &mut Context, num_args: usize) -> Ptr<BasicBlock> {
        let f = |self_ptr: Ptr<BasicBlock>| BasicBlock {
            self_ptr,
            args: Vec::new_init(num_args, |arg_idx| BlockArgument {
                def: Def { uses: vec![] },
                def_block: self_ptr,
                arg_idx,
            }),
            ops_list: OpsInBlock::new_empty(),
        };
        Self::alloc(ctx, f)
    }
}

impl ContainsLinkedList<Operation> for BasicBlock {
    fn get_head(&self, ctx: &Context) -> Option<Ptr<Operation>> {
        self.ops_list.first
    }

    fn get_tail(&self, ctx: &Context) -> Option<Ptr<Operation>> {
        self.ops_list.last
    }

    fn set_head(&mut self, ctx: &Context, head: Option<Ptr<Operation>>) {
        self.ops_list.first = head;
    }

    fn set_tail(&mut self, ctx: &Context, tail: Option<Ptr<Operation>>) {
        self.ops_list.last = tail;
    }
}

impl ArenaObj for BasicBlock {
    fn get_arena(ctx: &Context) -> &ArenaCell<Self> {
        &ctx.basic_blocks
    }
    fn get_arena_mut(ctx: &mut Context) -> &mut ArenaCell<Self> {
        &mut ctx.basic_blocks
    }
    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context) {
        let ops: Vec<_> = ptr.deref_mut(ctx).get_ops_iter(ctx).collect();
        for op in ops {
            ArenaObj::dealloc(op, ctx);
        }
    }
    fn remove_references(ptr: Ptr<Self>, ctx: &mut Context) {
        todo!()
    }

    fn get_self_ptr(&self) -> Ptr<Self> {
        self.self_ptr
    }
}
