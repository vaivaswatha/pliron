//! An operation is the basic unit of execution in the IR.
//! The general idea is similar to MLIR's
//! [Operation](https://mlir.llvm.org/docs/LangRef/#operations)

use std::marker::PhantomData;

use rustc_hash::FxHashMap;

use crate::{
    attribute::AttrObj,
    basic_block::BasicBlock,
    common_traits::{DisplayWithContext, Named, Verify},
    context::{private::ArenaObj, ArenaCell, Context, Ptr},
    debug_info,
    error::CompilerError,
    linked_list::{private, LinkedList},
    op::{self, OpId, OpObj},
    r#type::TypeObj,
    region::Region,
    use_def_lists::{DefNode, DefTrait, DefUseParticipant, Use, UseNode, Value},
    vec_exns::VecExtns,
    with_context::AttachContext,
};

mod visitor;
pub use visitor::*;

/// Represents the result of an [Operation].
pub(crate) struct OpResult {
    /// The def containing the list of this result's uses.
    pub(crate) def: DefNode<Value>,
    /// Get the [Operation] that this is a result of.
    def_op: Ptr<Operation>,
    /// Index of this result in the [Operation] that this is part of.
    res_idx: usize,
    /// [Type](crate::type::Type) of this operation result.
    ty: Ptr<TypeObj>,
}

impl OpResult {
    /// Get the [Type](crate::type::Type) of this operation result.
    pub fn get_type(&self) -> Ptr<TypeObj> {
        self.ty
    }
}

impl From<&OpResult> for Value {
    fn from(value: &OpResult) -> Self {
        Value::OpResult {
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

/// Basic unit of execution. May or may not be in a [BasicBlock].
pub struct Operation {
    /// OpId of self.
    pub(crate) opid: OpId,
    /// A [Ptr] to self.
    pub(crate) self_ptr: Ptr<Operation>,
    /// [Results](OpResult) defined by self.
    pub(crate) results: Vec<OpResult>,
    /// [Operand]s used by self.
    pub(crate) operands: Vec<Operand<Value>>,
    /// Control-flow-graph successors.
    pub(crate) successors: Vec<Operand<Ptr<BasicBlock>>>,
    /// Links to the parent [BasicBlock] and
    /// previous and next [Operation]s in the block.
    pub(crate) block_links: BlockLinks,
    /// A dictionary of attributes.
    pub attributes: FxHashMap<&'static str, AttrObj>,
    /// Regions contained inside this operation.
    pub(crate) regions: Vec<Ptr<Region>>,
}

impl PartialEq for Operation {
    fn eq(&self, other: &Self) -> bool {
        self.self_ptr == other.self_ptr
    }
}

impl private::LinkedList for Operation {
    type ContainerType = BasicBlock;
    fn set_next(&mut self, next: Option<Ptr<Self>>) {
        self.block_links.next_op = next;
    }
    fn set_prev(&mut self, prev: Option<Ptr<Self>>) {
        self.block_links.prev_op = prev;
    }
    fn set_container(&mut self, container: Option<Ptr<BasicBlock>>) {
        self.block_links.parent_block = container;
    }
}

impl LinkedList for Operation {
    fn get_next(&self) -> Option<Ptr<Self>> {
        self.block_links.next_op
    }
    fn get_prev(&self) -> Option<Ptr<Self>> {
        self.block_links.prev_op
    }
    fn get_container(&self) -> Option<Ptr<BasicBlock>> {
        self.block_links.parent_block
    }
}

impl Operation {
    /// Create a new, unlinked (i.e., not in a basic block) operation.
    pub fn new(
        ctx: &mut Context,
        opid: OpId,
        result_types: Vec<Ptr<TypeObj>>,
        operands: Vec<Value>,
        num_regions: usize,
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
                def: DefNode::new(),
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
            .map(|(opd_idx, def)| Operand::new(ctx, *def, newop, opd_idx))
            .collect();
        newop.deref_mut(ctx).operands = operands;
        newop.deref_mut(ctx).regions = Vec::new_init(num_regions, |_| Region::new(ctx, newop));

        newop
    }

    /// Number of results this operation has.
    pub fn get_num_results(&self) -> usize {
        self.results.len()
    }

    /// Get idx'th result as a Value.
    pub fn get_result(&self, idx: usize) -> Option<Value> {
        self.results.get(idx).map(|res| res.into())
    }

    /// Does any result of this operation have a use?
    pub fn has_use(&self) -> bool {
        self.results.iter().any(|res| res.def.has_use())
    }

    /// Total number of uses (across all results).
    pub fn num_uses(&self) -> usize {
        self.results
            .iter()
            .fold(0, |count, res| count + res.def.num_uses())
    }

    /// Get type of the idx'th result.
    pub fn get_type(&self, idx: usize) -> Option<Ptr<TypeObj>> {
        self.results.get(idx).map(|res| res.ty)
    }

    /// Get number of operands.
    pub fn get_num_operands(&self) -> usize {
        self.operands.len()
    }

    /// Get a reference to the opd_idx'th operand.
    pub fn get_operand(&self, opd_idx: usize) -> Option<Value> {
        self.operands.get(opd_idx).map(|opd| opd.get_def())
    }

    /// Replace opd_idx'th operand with `other`.
    pub fn replace_operand(&mut self, ctx: &Context, opd_idx: usize, other: Value) {
        self.operands
            .get_mut(opd_idx)
            .unwrap_or_else(|| panic!("No operand at index {}", opd_idx))
            .replace(ctx, other);
    }

    /// Get number of successors
    pub fn get_num_successors(&self) -> usize {
        self.successors.len()
    }

    /// Get a reference to the opd_idx'th successor.
    pub fn get_successor(&self, opd_idx: usize) -> Option<Ptr<BasicBlock>> {
        self.successors.get(opd_idx).map(|succ| succ.get_def())
    }

    /// Replace opd_idx'th successor with `other`.
    pub fn replace_successor(&mut self, ctx: &Context, opd_idx: usize, other: Ptr<BasicBlock>) {
        self.successors
            .get_mut(opd_idx)
            .unwrap_or_else(|| panic!("No successor at index {}", opd_idx))
            .replace(ctx, other);
    }

    /// Get an iterator on the successors.
    pub fn successors(&self) -> impl Iterator<Item = Ptr<BasicBlock>> + '_ {
        self.successors.iter().map(|opd| opd.get_def())
    }

    /// Create an OpObj corresponding to self.
    pub fn get_op(&self, ctx: &Context) -> OpObj {
        op::from_operation(ctx, self.self_ptr)
    }

    /// Get a [Ptr] to the `reg_idx`th region.
    pub fn get_region(&self, reg_idx: usize) -> Option<Ptr<Region>> {
        self.regions.get(reg_idx).cloned()
    }

    /// Erase `reg_idx`'th region.
    pub fn erase_region(ptr: Ptr<Self>, ctx: &mut Context, reg_idx: usize) {
        let reg = *ptr.deref(ctx).regions.get(reg_idx).unwrap();
        Region::drop_all_uses(reg, ctx);
        ptr.deref_mut(ctx).regions.retain(|r| *r != reg);
        ArenaObj::dealloc(reg, ctx);
    }

    /// Get the OpId of the Op of this Operation.
    pub fn get_opid(&self) -> OpId {
        self.opid.clone()
    }

    /// Drop all uses that this operation holds.
    pub fn drop_all_uses(ptr: Ptr<Self>, ctx: &mut Context) {
        // The operands cease to be a use of their definitions.
        let operands = std::mem::take(&mut (ptr.deref_mut(ctx).operands));
        for opd in operands {
            opd.drop(ctx);
        }
        // The successors cease to be a use of their definitions.
        let successors = std::mem::take(&mut (ptr.deref_mut(ctx).successors));
        for succ in successors {
            succ.drop(ctx);
        }

        let regions = ptr.deref(ctx).regions.clone();
        for region in regions {
            Region::drop_all_uses(region, ctx);
        }
    }

    /// Unlink and deallocate this operation and everything that it contains.
    /// There must not be any uses.
    pub fn erase(ptr: Ptr<Self>, ctx: &mut Context) {
        Self::drop_all_uses(ptr, ctx);
        assert!(
            !ptr.deref(ctx).has_use(),
            "Operation with use(s) being erased"
        );
        if ptr.is_linked(ctx) {
            ptr.unlink(ctx);
        }
        ArenaObj::dealloc(ptr, ctx);
    }

    /// Get a reference to the idx'th result.
    pub(crate) fn get_result_ref(&self, idx: usize) -> Option<&OpResult> {
        self.results.get(idx)
    }

    /// Get a mutable reference to the idx'th result.
    pub(crate) fn get_result_mut(&mut self, idx: usize) -> Option<&mut OpResult> {
        self.results.get_mut(idx)
    }

    /// Get a reference to the opd_idx'th operand.
    pub(crate) fn get_operand_ref(&self, opd_idx: usize) -> Option<&Operand<Value>> {
        self.operands.get(opd_idx)
    }

    /// Get a mutable reference to the opd_idx'th operand.
    pub(crate) fn get_operand_mut(&mut self, opd_idx: usize) -> Option<&mut Operand<Value>> {
        self.operands.get_mut(opd_idx)
    }

    /// Get a reference to the opd_idx'th successor.
    pub(crate) fn get_successor_ref(&self, opd_idx: usize) -> Option<&Operand<Ptr<BasicBlock>>> {
        self.successors.get(opd_idx)
    }

    /// Get a mutable reference to the opd_idx'th successor.
    pub(crate) fn get_successor_mut(
        &mut self,
        opd_idx: usize,
    ) -> Option<&mut Operand<Ptr<BasicBlock>>> {
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
    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context) {
        let regions = ptr.deref(ctx).regions.clone();
        for region in regions {
            ArenaObj::dealloc(region, ctx);
        }
    }
    fn get_self_ptr(&self, _ctx: &Context) -> Ptr<Self> {
        self.self_ptr
    }
}

/// Container for a [Use] in an [Operation].
pub(crate) struct Operand<T: DefUseParticipant> {
    pub(crate) r#use: UseNode<T>,
    /// This is the `opd_idx`'th operand of [user_op](Self::user_op).
    pub(crate) opd_idx: usize,
    /// The [Operation] that contains this [Use]
    pub(crate) user_op: Ptr<Operation>,
}

impl<T: DefUseParticipant + DefTrait> Operand<T> {
    /// Get the definition of this use.
    fn get_def(&self) -> T {
        self.r#use.get_def()
    }

    /// Drop this use, removing self from list of its definition's uses.
    fn drop(&self, ctx: &Context) {
        self.get_def().get_defnode_mut(ctx).remove_use(self.into());
    }

    /// Replace this operand to use another definition.
    fn replace(&mut self, ctx: &Context, other: T) {
        let user_op = self.user_op;
        let opd_idx = self.opd_idx;
        self.drop(ctx);
        *self = Self::new(ctx, other, user_op, opd_idx);
    }

    /// As `user_op`'s `opd_idx`'th operand, create a new Operand.
    fn new(ctx: &Context, def: T, user_op: Ptr<Operation>, opd_idx: usize) -> Operand<T> {
        Operand {
            r#use: def.get_defnode_mut(ctx).add_use(
                def,
                Use {
                    op: user_op,
                    opd_idx,
                    _dummy: PhantomData,
                },
            ),
            user_op,
            opd_idx,
        }
    }
}

impl<T: DefUseParticipant> From<&Operand<T>> for Use<T> {
    fn from(value: &Operand<T>) -> Self {
        Use {
            op: value.user_op,
            opd_idx: value.opd_idx,
            _dummy: PhantomData,
        }
    }
}

impl<T: DefUseParticipant> AttachContext for Operand<T> {}
impl<T: DefUseParticipant + Named> DisplayWithContext for Operand<T> {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.r#use.get_def().get_name(ctx))
    }
}

impl<T: DefUseParticipant + DefTrait> Verify for Operand<T> {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
        if !self
            .r#use
            .get_def()
            .get_defnode_ref(ctx)
            .has_use_of(&self.into())
        {
            Err(CompilerError::VerificationError {
                msg: "Operand is not a use of its def".to_string(),
            })
        } else {
            Ok(())
        }
    }
}

impl Verify for Operation {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
        for _attr in self.attributes.values() {
            // TODO.
            // attr.verify(ctx)?;
            // attr.verify_interfaces(ctx)?;
        }
        for opd in &self.operands {
            opd.verify(ctx)?;
        }
        for region in &self.regions {
            region.verify(ctx)?;
        }
        self.get_op(ctx).verify(ctx)?;
        self.get_op(ctx).verify_interfaces(ctx)
    }
}

impl AttachContext for Operation {}
impl DisplayWithContext for Operation {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.get_op(ctx).fmt(ctx, f)
    }
}
