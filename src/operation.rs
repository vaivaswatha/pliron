use crate::{
    basic_block::BasicBlock,
    common_traits::{Stringable, Verify},
    context::{ArenaCell, ArenaObj, Context, Ptr},
    error::{self, CompilerError},
    linked_list::LinkedList,
    use_def_lists::{BlockDefDescr, Def, DefDescr, DefDescrTrait, Use, UseDescr, ValDefDescr},
    vec_exns::VecExtns,
};

/// Represents the result of an [Operation].
#[derive(Debug)]
pub struct OpResult {
    /// The def containing the list of this result's uses.
    pub(crate) def: Def,
    /// Get the [Operation] that this is a result of.
    pub(crate) def_op: Ptr<Operation>,
    /// Index of this result in the [Operation] that this is part of.
    pub(crate) res_idx: usize,
}

impl OpResult {
    /// A [Ptr] to the [Operation] that this is a result of.
    pub fn get_def_op(&self) -> Ptr<Operation> {
        self.def_op
    }

    /// Index of this result in the [Operation] that this is part of.
    pub fn get_res_idx(&self) -> usize {
        self.res_idx
    }

    /// Build a [DefDescr] that describes this value.
    pub fn build_def_descr(&self) -> DefDescr<ValDefDescr> {
        DefDescr(ValDefDescr::OpResult {
            op: self.def_op,
            res_idx: self.res_idx,
        })
    }
}

/// Links an [Operation] with other operations and the container [BasicBlock]
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
    pub operands: Vec<Operand<ValDefDescr>>,
    pub successors: Vec<Operand<BlockDefDescr>>,
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
    pub fn new(
        ctx: &mut Context,
        num_results: usize,
        operands: Vec<ValDefDescr>,
    ) -> Ptr<Operation> {
        let f = |self_ptr: Ptr<Operation>| Operation {
            self_ptr,
            results: Vec::new_init(num_results, |res_idx| OpResult {
                def: Def::new(),
                def_op: self_ptr,
                res_idx,
            }),
            operands: vec![],
            successors: vec![],
            block_links: BlockLinks::new_unlinked(),
        };
        let newop = Self::alloc(ctx, f);
        let operands: Vec<Operand<ValDefDescr>> = operands
            .iter()
            .enumerate()
            .map(|(opd_idx, def)| Operand {
                r#use: def.add_use(ctx, UseDescr { op: newop, opd_idx }),
                opd_idx,
                user_op: newop,
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
    pub fn get_operand(&self, opd_idx: usize) -> Option<&Operand<ValDefDescr>> {
        self.operands.get(opd_idx)
    }

    /// Get a mutable reference to the opd_idx'th operand.
    pub fn get_operand_mut(&mut self, opd_idx: usize) -> Option<&mut Operand<ValDefDescr>> {
        self.operands.get_mut(opd_idx)
    }

    /// Get a reference to the opd_idx'th successor.
    pub fn get_successor(&self, opd_idx: usize) -> Option<&Operand<BlockDefDescr>> {
        self.successors.get(opd_idx)
    }

    /// Get a mutable reference to the opd_idx'th successor.
    pub fn get_successor_mut(&mut self, opd_idx: usize) -> Option<&mut Operand<BlockDefDescr>> {
        self.successors.get_mut(opd_idx)
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

/// Container for a [Use] in an [Operation].
#[derive(Debug)]
pub struct Operand<T: DefDescrTrait> {
    pub(crate) r#use: Use<T>,
    /// This is the `opd_idx`'th operand of [user_op](Self::user_op).
    pub(crate) opd_idx: usize,
    /// The [Operation] that contains this [Use]
    pub(crate) user_op: Ptr<Operation>,
}

impl<T: DefDescrTrait> Operand<T> {
    /// i'th operand in the [Operation] that contains this.
    pub fn get_opd_idx(&self) -> usize {
        self.opd_idx
    }

    /// Get the [Operation] of which this is an operand.
    pub fn get_user_op(&self) -> Ptr<Operation> {
        self.user_op
    }
}

impl<T: DefDescrTrait> Stringable for Operand<T> {
    fn to_string(&self, _ctx: &Context) -> String {
        todo!()
    }
}

impl<T: DefDescrTrait> Verify for Operand<T> {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
        match self.r#use.def.0.get_use(ctx, self.r#use.use_idx) {
            Some(descr) if descr.op == self.user_op || descr.opd_idx == self.opd_idx => Ok(()),
            _ => Err(error::CompilerError::VerificationError {
                msg: format!(
                    "Definition of {} doesn't have a matching use at the specified position",
                    self.to_string(ctx)
                ),
            }),
        }
    }
}
