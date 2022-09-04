use crate::{
    basic_block::BasicBlock,
    context::{ArenaCell, ArenaObj, Context, Ptr},
    linked_list::LinkedList,
    use_def_lists::{Def, DefDescr, Use, UseDescr},
    value::Value,
    vec_exns::VecExtns,
};

/// Represents the result of an Operation.
#[derive(Debug)]
pub struct OpResult {
    def: Def,
    def_op: Ptr<Operation>,
    res_idx: usize,
}

impl Value for OpResult {
    fn get_defining_op(&self) -> Option<Ptr<Operation>> {
        Some(self.def_op)
    }

    fn get_parent_block(&self, ctx: &Context) -> Option<Ptr<BasicBlock>> {
        self.def_op.deref(ctx).block_links.parent_block
    }

    fn get_def_index(&self) -> usize {
        self.res_idx
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
            def: DefDescr::OpResult {
                op: self.get_defining_op().unwrap(),
                res_idx: self.get_def_index(),
            },
            use_idx,
        }
    }
}

/// Links an operation with other operations and the container basic block.
#[derive(Debug)]
pub struct BlockLinks {
    /// Parent block of this operation.
    pub parent_block: Option<Ptr<BasicBlock>>,
    /// The next operation in the basic block's list of operations.
    pub next_op: Option<Ptr<Operation>>,
    /// The previous operation in the basic block's list of operations.
    pub prev_op: Option<Ptr<Operation>>,
}

impl BlockLinks {
    pub fn new_unlinked() -> BlockLinks {
        BlockLinks {
            parent_block: None,
            next_op: None,
            prev_op: None,
        }
    }
}

/// An operation is the basic unit of execution in the IR.
/// The general idea is similar to MLIR's
/// [Operation](https://mlir.llvm.org/docs/LangRef/#operations)
#[derive(Debug)]
pub struct Operation {
    pub self_ptr: Ptr<Operation>,
    pub results: Vec<OpResult>,
    pub operands: Vec<Operand>,
    pub block_links: BlockLinks,
}

impl PartialEq for Operation {
    fn eq(&self, other: &Self) -> bool {
        self.self_ptr == other.self_ptr
    }
}

impl LinkedList for Operation {
    type ContainerType = BasicBlock;

    fn get_next(&self) -> Option<Ptr<Self>> {
        self.block_links.next_op
    }

    fn get_prev(&self) -> Option<Ptr<Self>> {
        self.block_links.prev_op
    }

    fn set_next(&mut self, next: Option<Ptr<Self>>) {
        self.block_links.next_op = next;
    }

    fn set_prev(&mut self, prev: Option<Ptr<Self>>) {
        self.block_links.prev_op = prev;
    }

    fn get_container(&self) -> Option<Ptr<BasicBlock>> {
        self.block_links.parent_block
    }

    fn set_container(&mut self, container: Option<Ptr<BasicBlock>>) {
        self.block_links.parent_block = container;
    }
}

impl Operation {
    /// Create a new, unlinked (i.e., not in a basic block) operation.
    pub fn new(ctx: &mut Context, num_results: usize, operands: Vec<DefDescr>) -> Ptr<Operation> {
        let f = |self_ptr: Ptr<Operation>| Operation {
            self_ptr,
            results: Vec::new_init(num_results, |res_idx| OpResult {
                def: Def { uses: vec![] },
                def_op: self_ptr,
                res_idx,
            }),
            operands: vec![],
            block_links: BlockLinks::new_unlinked(),
        };
        let newop = Self::alloc(ctx, f);
        let operands: Vec<Operand> = operands
            .iter()
            .enumerate()
            .map(|(opd_idx, def)| {
                let mut defval = def.get_value_ref_mut(ctx);
                let r#use = (*defval).add_use(UseDescr { op: newop, opd_idx });
                Operand {
                    r#use,
                    opd_idx,
                    user_op: newop,
                }
            })
            .collect();
        newop.deref_mut(ctx).operands = operands;
        newop
    }

    /// Get a reference to the idx'th result.
    pub fn get_result(&self, idx: usize) -> Option<&OpResult> {
        self.results.get(idx)
    }

    /// Get a mutable reference to the idx'th result.
    pub fn get_result_mut(&mut self, idx: usize) -> Option<&mut OpResult> {
        self.results.get_mut(idx)
    }

    /// Get a reference to the opd_idx'th operand.
    pub fn get_operand(&self, opd_idx: usize) -> Option<&Operand> {
        self.operands.get(opd_idx)
    }

    /// Get a mutable reference to the opd_idx'th operand.
    pub fn get_operand_mut(&mut self, opd_idx: usize) -> Option<&mut Operand> {
        self.operands.get_mut(opd_idx)
    }
}

impl ArenaObj for Operation {
    fn get_arena(ctx: &Context) -> &ArenaCell<Self> {
        &ctx.operations
    }
    fn get_arena_mut(ctx: &mut Context) -> &mut ArenaCell<Self> {
        &mut ctx.operations
    }
    fn dealloc_sub_objects(_ptr: Ptr<Self>, _ctx: &mut Context) {
        todo!()
    }
    fn remove_references(ptr: Ptr<Self>, ctx: &mut Context) {
        // Unlink from parent block, if there's one.
        if ptr.deref(ctx).block_links.parent_block.is_some() {
            ptr.deref_mut(ctx).remove(ctx);
        }
    }
    fn get_self_ptr(&self, _ctx: &Context) -> Ptr<Self> {
        self.self_ptr
    }
}

/// Container for a Use in an operation.
#[derive(Debug)]
pub struct Operand {
    r#use: Use,
    opd_idx: usize,
    user_op: Ptr<Operation>,
}

impl Operand {
    /// i'th operand in the Operation that contains this.
    pub fn get_opd_idx(&self) -> usize {
        self.opd_idx
    }

    /// Get the operation of which this is an operand.
    pub fn get_user_op(&self) -> Ptr<Operation> {
        self.user_op
    }

    /// Build a UseRef referring to this operand.
    pub fn build_useref(&self) -> UseDescr {
        UseDescr {
            op: self.get_user_op(),
            opd_idx: self.get_opd_idx(),
        }
    }

    /// Update the operand to be the Use of a different Def.
    pub fn replace_def(&mut self, new_val: Use) {
        self.r#use = new_val;
    }
}
