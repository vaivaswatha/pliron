use rustc_hash::FxHashMap;

use crate::{
    attribute::AttrObj,
    basic_block::BasicBlock,
    common_traits::{DisplayWithContext, Named, Verify},
    context::{ArenaCell, ArenaObj, Context, Ptr},
    debug_info,
    error::CompilerError,
    linked_list::LinkedList,
    op::{self, OpId, OpObj},
    r#type::TypeObj,
    region::Region,
    use_def_lists::{BlockDef, Def, DefDescrTrait, Use, UseDescr, ValDef},
    with_context::AttachContext,
};

/// Represents the result of an [Operation].
pub struct OpResult {
    /// The def containing the list of this result's uses.
    pub(crate) def: Def,
    /// Get the [Operation] that this is a result of.
    def_op: Ptr<Operation>,
    /// Index of this result in the [Operation] that this is part of.
    res_idx: usize,
    /// [Type](crate::type::Type) of this operation result.
    ty: Ptr<TypeObj>,
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

    /// Get the [Type](crate::type::Type) of this operation result.
    pub fn get_type(&self) -> Ptr<TypeObj> {
        self.ty
    }
}

impl From<&OpResult> for ValDef {
    fn from(value: &OpResult) -> Self {
        ValDef::OpResult {
            op: value.def_op,
            res_idx: value.res_idx,
        }
    }
}

impl Named for OpResult {
    fn get_name(&self, ctx: &Context) -> String {
        debug_info::get_operation_result_name(ctx, self.def_op, self.res_idx)
            .unwrap_or_else(|| self.def_op.make_name("op") + &format!("[{}]", self.res_idx))
    }
}

/// Links an [Operation] with other operations and the container [BasicBlock]
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
pub struct Operation {
    /// OpId of self.
    pub opid: OpId,
    /// A [Ptr] to self.
    pub self_ptr: Ptr<Operation>,
    /// [Results](OpResult) defined by self.
    pub results: Vec<OpResult>,
    /// [Operand]s used by self.
    pub operands: Vec<Operand<ValDef>>,
    /// Control-flow-graph successors.
    pub successors: Vec<Operand<BlockDef>>,
    /// Links to the parent [BasicBlock] and
    /// previous and next [Operation]s in the block.
    pub block_links: BlockLinks,
    /// A dictionary of attributes.
    pub attributes: FxHashMap<&'static str, AttrObj>,
    /// Regions contained inside this operation.
    pub regions: Vec<Ptr<Region>>,
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
        opid: OpId,
        result_types: Vec<Ptr<TypeObj>>,
        operands: Vec<ValDef>,
    ) -> Ptr<Operation> {
        let f = |self_ptr: Ptr<Operation>| Operation {
            opid,
            self_ptr,
            results: vec![],
            operands: vec![],
            successors: vec![],
            block_links: BlockLinks::new_unlinked(),
            attributes: FxHashMap::default(),
            regions: vec![],
        };

        // Create the new Operation.
        let newop = Self::alloc(ctx, f);
        // Update the results (we can't do this easily during creation).
        let results = result_types
            .into_iter()
            .enumerate()
            .map(|(res_idx, ty)| OpResult {
                def: Def::new(),
                def_op: newop,
                ty,
                res_idx,
            })
            .collect();
        newop.deref_mut(ctx).results = results;
        // Update the operands (we can't do this easily during creation).
        let operands = operands
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

    /// Number of results this operation has.
    pub fn get_num_results(&self) -> usize {
        self.results.len()
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
    pub fn get_operand(&self, opd_idx: usize) -> Option<&Operand<ValDef>> {
        self.operands.get(opd_idx)
    }

    /// Get a mutable reference to the opd_idx'th operand.
    pub fn get_operand_mut(&mut self, opd_idx: usize) -> Option<&mut Operand<ValDef>> {
        self.operands.get_mut(opd_idx)
    }

    /// Get number of operands.
    pub fn get_num_operands(&self) -> usize {
        self.operands.len()
    }

    /// Get a reference to the opd_idx'th successor.
    pub fn get_successor(&self, opd_idx: usize) -> Option<&Operand<BlockDef>> {
        self.successors.get(opd_idx)
    }

    /// Get a mutable reference to the opd_idx'th successor.
    pub fn get_successor_mut(&mut self, opd_idx: usize) -> Option<&mut Operand<BlockDef>> {
        self.successors.get_mut(opd_idx)
    }

    /// Create an OpObj corresponding to self.
    pub fn get_op(&self, ctx: &Context) -> OpObj {
        op::from_operation(ctx, self.self_ptr)
    }

    /// Get the OpId of the Op of this Operation.
    pub fn get_opid(&self) -> OpId {
        self.opid.clone()
    }
}

impl ArenaObj for Operation {
    fn get_arena(ctx: &Context) -> &ArenaCell<Self> {
        &ctx.operations
    }
    fn get_arena_mut(ctx: &mut Context) -> &mut ArenaCell<Self> {
        &mut ctx.operations
    }
    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context) {
        let regions = ptr.deref(ctx).regions.clone();
        for region in regions {
            ArenaObj::dealloc(region, ctx);
        }
    }
    fn remove_references(ptr: Ptr<Self>, ctx: &mut Context) {
        // Unlink from parent block, if there's one.
        if ptr.deref(ctx).block_links.parent_block.is_some() {
            ptr.remove(ctx);
        }
    }
    fn get_self_ptr(&self, _ctx: &Context) -> Ptr<Self> {
        self.self_ptr
    }
}

/// Container for a [Use] in an [Operation].
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

    /// Build a UseDescr describing this operand.
    pub fn build_use_descr(&self) -> UseDescr {
        UseDescr {
            op: self.user_op,
            opd_idx: self.opd_idx,
        }
    }
}

impl<T: DefDescrTrait> AttachContext for Operand<T> {}
impl<T: DefDescrTrait + Named> DisplayWithContext for Operand<T> {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.r#use.def.get_name(ctx))
    }
}

impl<T: DefDescrTrait> Verify for Operand<T> {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
        if !self.r#use.def.0.has_use_of(ctx, &self.build_use_descr()) {}
        Ok(())
    }
}

impl Verify for Operation {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
        self.get_op(ctx).verify(ctx)
    }
}

impl AttachContext for Operation {}
impl DisplayWithContext for Operation {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.get_op(ctx).fmt(ctx, f)
    }
}
