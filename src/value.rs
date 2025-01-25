//! SSA [Value]s: Use-Def and Def-Use Graph.
//! At the core of the IR infrastructure are SSA def-use and use-def chains.
//! Use-def and def-use chains are composed of four key structures:
//!   - [Value] describes a value definition, either a block argument, or an operation result.
//!   - [`Ptr<BasicBlock>`] describes a block definition.
//!     Its uses are in the predecessor branch operations.
//!   - [Use] describes the use of a definition.
//!     This may describe either a [Value] use (as operand in an [Operation])
//!     or a [BasicBlock] use (as successor of an [Operation]).

use rustc_hash::FxHashSet;
use std::{
    cell::{Ref, RefMut},
    hash::Hash,
    marker::PhantomData,
};

use crate::{
    basic_block::BasicBlock,
    common_traits::Named,
    context::{Context, Ptr},
    identifier::Identifier,
    linked_list::{ContainsLinkedList, LinkedList},
    operation::Operation,
    printable::Printable,
    r#type::{TypeObj, Typed},
};

/// def-use chains are implemented for [Value]s and `Ptr<BasicBlock`.
pub trait DefUseParticipant: Copy + Hash + Eq {}
impl DefUseParticipant for Value {}
impl DefUseParticipant for Ptr<BasicBlock> {}

/// A def node contains a list of its uses.
pub(crate) struct DefNode<T: DefUseParticipant> {
    /// The list of uses of this Def.
    uses: FxHashSet<Use<T>>,
}

impl<T: DefUseParticipant> DefNode<T> {
    /// Create a new definition.
    pub(crate) fn new() -> DefNode<T> {
        DefNode {
            uses: FxHashSet::default(),
        }
    }

    /// Does the definition have a use?
    pub(crate) fn is_used(&self) -> bool {
        !self.uses.is_empty()
    }

    /// How many uses does this definition have?
    pub(crate) fn num_uses(&self) -> usize {
        self.uses.len()
    }

    /// Does this definition have a [Use] of `use` ?
    pub(crate) fn has_use_of(&self, r#use: &Use<T>) -> bool {
        self.uses.contains(r#use)
    }

    /// Get a reference to all [Use]es.
    pub(crate) fn uses(&self) -> impl Iterator<Item = Use<T>> + '_ {
        self.uses.iter().cloned()
    }

    /// This definition has a new use. Track it and return a corresponding [Use].
    /// The returned [UseNode] is to be used in constructing an operand etc.
    pub(crate) fn add_use(&mut self, self_descr: T, r#use: Use<T>) -> UseNode<T> {
        if !self.uses.insert(r#use) {
            panic!("Def: Attempt to insert an existing use");
        }
        UseNode { def: self_descr }
    }

    /// Remove `use` from the underlying definition.
    pub(crate) fn remove_use(&mut self, r#use: Use<T>) {
        if !self.uses.remove(&r#use) {
            panic!("Def: Attempt to remove a use that doesn't exist");
        }
    }

    /// Replace the given use of the underlying definition `this` with `other`.
    pub(crate) fn replace_use_with(ctx: &Context, this: &T, r#use: &Use<T>, other: &T)
    where
        T: DefTrait + UseTrait,
    {
        if std::ptr::eq(&*this.get_defnode_ref(ctx), &*other.get_defnode_ref(ctx)) {
            return;
        }

        // Add r#use as a use of `other` and replace the [UseNode].
        let new_use_node = other.get_defnode_mut(ctx).add_use(*other, *r#use);
        *T::get_usenode_mut(r#use, ctx) = new_use_node;

        // `this` will no longer have r#use as a use.
        this.get_defnode_mut(ctx).uses.remove(r#use);
    }
}

/// Interface for [UseNode] wrappers.
pub(crate) trait UseTrait: DefUseParticipant {
    /// Get a mutable reference to the [UseNode] described by this  use.
    fn get_usenode_mut<'a>(r#use: &Use<Self>, ctx: &'a Context) -> RefMut<'a, UseNode<Self>>;
}

/// Interface for [DefNode] wrappers.
pub(crate) trait DefTrait: DefUseParticipant {
    /// Get a reference to the underlying [DefNode].
    fn get_defnode_ref<'a>(&self, ctx: &'a Context) -> Ref<'a, DefNode<Self>>;
    /// Get a mutable reference to the underlying [DefNode].
    fn get_defnode_mut<'a>(&self, ctx: &'a Context) -> RefMut<'a, DefNode<Self>>;
}

/// Describes a value definition.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Value {
    OpResult {
        op: Ptr<Operation>,
        res_idx: usize,
    },
    BlockArgument {
        block: Ptr<BasicBlock>,
        arg_idx: usize,
    },
}

impl Value {
    /// How many uses does this definition have?
    pub fn num_uses(&self, ctx: &Context) -> usize {
        self.get_defnode_ref(ctx).num_uses()
    }

    /// Get all uses of this value.
    pub fn uses(&self, ctx: &Context) -> Vec<Use<Value>> {
        self.get_defnode_ref(ctx).uses().collect()
    }

    /// Does this definition have any [Use]?
    pub fn is_used(&self, ctx: &Context) -> bool {
        self.get_defnode_ref(ctx).is_used()
    }

    /// Replace uses of the underlying definition, that satisfy `pred`, with `other`.
    pub fn replace_some_uses_with<P: Fn(&Context, &Use<Value>) -> bool>(
        &self,
        ctx: &Context,
        predicate: P,
        other: &Value,
    ) {
        // We collect because we don't want to keep the defnode locked up.
        let touched_uses: FxHashSet<_> = self
            .get_defnode_ref(ctx)
            .uses
            .iter()
            .filter(|r#use| predicate(ctx, r#use))
            .cloned()
            .collect();
        for r#use in &touched_uses {
            DefNode::replace_use_with(ctx, self, r#use, other);
        }
    }

    /// Replace the given use of `this` [Value] with `other`.
    pub fn replace_use_with(&self, ctx: &Context, r#use: Use<Value>, other: &Value) {
        DefNode::replace_use_with(ctx, self, &r#use, other);
    }
}

impl Typed for Value {
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        match self {
            Value::OpResult { op, res_idx } => op.deref(ctx).get_result_ref(*res_idx).get_type(),
            Value::BlockArgument { block, arg_idx } => {
                block.deref(ctx).get_argument_ref(*arg_idx).get_type(ctx)
            }
        }
    }
}

impl Named for Value {
    fn given_name(&self, ctx: &Context) -> Option<Identifier> {
        match self {
            Value::OpResult { op, res_idx } => {
                op.deref(ctx).get_result_ref(*res_idx).given_name(ctx)
            }
            Value::BlockArgument { block, arg_idx } => {
                block.deref(ctx).get_argument_ref(*arg_idx).given_name(ctx)
            }
        }
    }

    fn id(&self, ctx: &Context) -> Identifier {
        match self {
            Value::OpResult { op, res_idx } => op.deref(ctx).get_result_ref(*res_idx).id(ctx),
            Value::BlockArgument { block, arg_idx } => {
                block.deref(ctx).get_argument_ref(*arg_idx).id(ctx)
            }
        }
    }
}

impl Printable for Value {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &crate::printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "{}", self.unique_name(ctx))
    }
}

impl DefTrait for Value {
    fn get_defnode_ref<'a>(&self, ctx: &'a Context) -> Ref<'a, DefNode<Self>> {
        match self {
            Self::OpResult { op, res_idx } => {
                let op = op.deref(ctx);
                Ref::map(op, |opref| &opref.get_result_ref(*res_idx).def)
            }
            Self::BlockArgument { block, arg_idx } => {
                let block = block.deref(ctx);
                Ref::map(block, |blockref| &blockref.get_argument_ref(*arg_idx).def)
            }
        }
    }

    fn get_defnode_mut<'a>(&self, ctx: &'a Context) -> RefMut<'a, DefNode<Self>> {
        match self {
            Self::OpResult { op, res_idx } => {
                let op = op.deref_mut(ctx);
                RefMut::map(op, |opref| &mut opref.get_result_mut(*res_idx).def)
            }
            Self::BlockArgument { block, arg_idx } => {
                let block = block.deref_mut(ctx);
                RefMut::map(block, |blockref| {
                    &mut blockref.get_argument_mut(*arg_idx).def
                })
            }
        }
    }
}

impl UseTrait for Value {
    fn get_usenode_mut<'a>(r#use: &Use<Self>, ctx: &'a Context) -> RefMut<'a, UseNode<Value>> {
        let op = r#use.op.deref_mut(ctx);
        RefMut::map(op, |opref| &mut opref.get_operand_mut(r#use.opd_idx).r#use)
    }
}

impl Ptr<BasicBlock> {
    /// Does this block a predecessor?
    pub fn has_pred(&self, ctx: &Context) -> bool {
        self.deref(ctx).preds.is_used()
    }

    /// Number of predecessors to this block.
    pub fn num_preds(&self, ctx: &Context) -> usize {
        self.deref(ctx).preds.num_uses()
    }

    /// Get all predecessors of this block.
    pub fn preds(&self, ctx: &Context) -> Vec<Ptr<BasicBlock>> {
        self.deref(ctx)
            .preds
            .uses()
            .map(|r#use| {
                r#use
                    .op
                    .deref(ctx)
                    .get_container()
                    .expect("Terminator branching to this block is not in any basic block")
            })
            .collect()
    }

    /// Checks whether self is a successor of `pred`.
    /// O(n) in the number of successors of `pred`.
    pub fn is_succ_of(&self, ctx: &Context, pred: Ptr<BasicBlock>) -> bool {
        // We do not check [Self::get_defnode_ref].uses here because
        // we'd have to go through them all. We do not have a Use<_>
        // object to directly check membership.
        pred.deref(ctx)
            .get_tail()
            .is_some_and(|pred_term| pred_term.deref(ctx).successors().any(|succ| self == &succ))
    }
    /// Retarget predecessors (that satisfy pred) to `other`.
    pub fn retarget_some_preds_to<P: Fn(&Context, Ptr<BasicBlock>) -> bool>(
        &self,
        ctx: &Context,
        predicate: P,
        other: Ptr<BasicBlock>,
    ) {
        let predicate = |ctx: &Context, r#use: &Use<Ptr<BasicBlock>>| {
            let pred_block = r#use
                .op
                .deref(ctx)
                .get_container()
                .expect("Predecessor block must be in a Region");
            predicate(ctx, pred_block)
        };

        // We collect because we don't want to keep the defnode locked up.
        let touched_uses: FxHashSet<_> = self
            .get_defnode_ref(ctx)
            .uses
            .iter()
            .filter(|r#use| predicate(ctx, r#use))
            .cloned()
            .collect();

        for r#use in &touched_uses {
            DefNode::replace_use_with(ctx, self, r#use, &other);
        }
    }

    /// Retarget the given pred (`block_use`) of `this` [`Ptr<BasicBlock>`] to `other`.
    pub fn retarget_pred_to(
        &self,
        ctx: &Context,
        block_use: Use<Ptr<BasicBlock>>,
        other: Ptr<BasicBlock>,
    ) {
        DefNode::replace_use_with(ctx, self, &block_use, &other);
    }
}

impl Named for Ptr<BasicBlock> {
    fn given_name(&self, ctx: &Context) -> Option<Identifier> {
        self.deref(ctx).given_name(ctx)
    }
    fn id(&self, ctx: &Context) -> Identifier {
        self.deref(ctx).id(ctx)
    }
}

impl DefTrait for Ptr<BasicBlock> {
    fn get_defnode_ref<'a>(&self, ctx: &'a Context) -> Ref<'a, DefNode<Self>> {
        let block = self.deref(ctx);
        Ref::map(block, |blockref| &blockref.preds)
    }

    fn get_defnode_mut<'a>(&self, ctx: &'a Context) -> RefMut<'a, DefNode<Self>> {
        let block = self.deref_mut(ctx);
        RefMut::map(block, |blockref| &mut blockref.preds)
    }
}

impl UseTrait for Ptr<BasicBlock> {
    fn get_usenode_mut<'a>(
        r#use: &Use<Ptr<BasicBlock>>,
        ctx: &'a Context,
    ) -> RefMut<'a, UseNode<Ptr<BasicBlock>>> {
        let op = r#use.op.deref_mut(ctx);
        RefMut::map(op, |opref| {
            &mut opref.get_successor_mut(r#use.opd_idx).r#use
        })
    }
}

/// A use node contains a pointer to its definition.
#[derive(Clone, Copy, Debug)]
pub(crate) struct UseNode<T: DefUseParticipant> {
    /// The definition that this is a use of.
    def: T,
}

impl<T: DefUseParticipant> UseNode<T> {
    pub(crate) fn get_def(&self) -> T {
        self.def
    }
}

/// Describes a [Value] or [BasicBlock] use.
#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub struct Use<T: DefUseParticipant> {
    /// Uses of a def can only be in an operation.
    pub op: Ptr<Operation>,
    /// Used as the i'th operand or successor of [op](Self::op).
    pub opd_idx: usize,
    pub(crate) _dummy: PhantomData<T>,
}
