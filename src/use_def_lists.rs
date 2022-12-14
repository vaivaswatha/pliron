//! # Use-Def and Def-Use Chains
//! Like in LLVM, at the core of the IR infrastructure are SSA use-def chains.
//! Use-def and def-use chains are composed of four key structures:
//!   - [Def] represents a definition. At its core, it is just a list of its uses.
//!   - [Use] represents a use of a definition. At its core, it is just a
//!     description of / pointer to its definition.
//!   - [UseDescr] describes a [Use], which is a pair composed of the [Operation] and the
//!     [Operand](crate::operation::Operand) in that operation, which together forms a use.
//!   - [DefDescr] describes a [Def], which is either the definition of a value
//!     (result of an operation / block argument) or a [BasicBlock].
//!     Def-use chains for basic blocks are used to track the predecessors of a block.

use rustc_hash::FxHashSet;
use std::cell::{Ref, RefMut};

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    operation::{Operand, Operation},
};

/// A definition is a list of its uses.
#[derive(Debug)]
pub struct Def {
    /// The list of uses of this Def.
    uses: FxHashSet<UseDescr>,
}

impl Def {
    /// Create a new definition.
    pub(crate) fn new() -> Def {
        Def {
            uses: FxHashSet::default(),
        }
    }
}

/// A trait for [definition descriptors](DefDescr).
pub trait DefDescrTrait: Copy + PartialEq {
    /// Get a reference to the underlying [Def].
    fn get_def<'a>(&self, ctx: &'a Context) -> Ref<'a, Def>;
    /// Get a mutable reference to the underlying [Def].
    fn get_def_mut<'a>(&self, ctx: &'a Context) -> RefMut<'a, Def>;

    /// Get a reference to the [Operand] described by `descr`.
    /// Checks that `descr` indeed is a [Use] of the underlying [Def].
    fn get_use_operand<'a>(
        &self,
        ctx: &'a Context,
        descr: &UseDescr,
    ) -> Option<Ref<'a, Operand<Self>>>;
    /// Get a reference to the [Operand] described by `descr`.
    /// Checks that `descr` indeed is a [Use] of the underlying [Def].
    fn get_use_operand_mut<'a>(
        &self,
        ctx: &'a Context,
        descr: &UseDescr,
    ) -> Option<RefMut<'a, Operand<Self>>>;

    /// How many uses does the [Def] corresponding to this [DefDescr] have?
    fn num_uses(&self, ctx: &Context) -> usize {
        self.get_def(ctx).uses.len()
    }

    /// Does this [Def] have any [Use]?
    fn has_use(&self, ctx: &Context) -> bool {
        !self.get_def(ctx).uses.is_empty()
    }

    /// Is `descr` a [Use] of this [Def]?
    fn has_use_of(&self, ctx: &Context, descr: &UseDescr) -> bool {
        self.get_def(ctx).uses.contains(descr)
    }

    /// Get a reference to this [Def]'s [Use]es.
    fn uses<'a>(&self, ctx: &'a Context) -> Ref<'a, FxHashSet<UseDescr>> {
        Ref::map(self.get_def(ctx), |def| &def.uses)
    }

    /// This definition has a new use. Track it and return a corresponding [Use].
    /// The returned [Use] is to be used in constructing an operand etc.
    fn add_use(&self, ctx: &Context, r#use: UseDescr) -> Use<Self>
    where
        Self: Sized,
    {
        if !self.get_def_mut(ctx).uses.insert(r#use) {
            panic!("Def: Attempt to insert an existing use");
        }
        Use {
            def: DefDescr::<Self>(*self),
        }
    }

    /// Remove `use` from the underlying [Def].
    fn remove_use(&self, ctx: &Context, r#use: UseDescr) {
        if !self.get_def_mut(ctx).uses.remove(&r#use) {
            panic!("Def: Attempt to remove a use that doesn't exist");
        }
    }

    /// Replace all uses of the underlying [Def] with `other`.
    fn replace_all_uses_with(&self, ctx: &Context, other: &Self) {
        if self == other {
            return;
        }
        for r#use in self.uses(ctx).iter() {
            let mut opd_ref = self.get_use_operand_mut(ctx, r#use).unwrap();
            opd_ref.r#use = other.add_use(ctx, *r#use);
        }
        // self will no longer have any uses.
        self.get_def_mut(ctx).uses.clear();
    }
}

/// Pointer to / describes a value definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValDefDescr {
    OpResult {
        op: Ptr<Operation>,
        res_idx: usize,
    },
    BlockArgument {
        block: Ptr<BasicBlock>,
        arg_idx: usize,
    },
}
impl DefDescrTrait for ValDefDescr {
    fn get_def<'a>(&self, ctx: &'a Context) -> Ref<'a, Def> {
        match self {
            Self::OpResult { op, res_idx } => {
                let op = op.deref(ctx);
                Ref::map(op, |opref| &opref.get_result(*res_idx).unwrap().def)
            }
            Self::BlockArgument { block, arg_idx } => {
                let block = block.deref(ctx);
                Ref::map(block, |blockref| {
                    &blockref.get_argument(*arg_idx).unwrap().def
                })
            }
        }
    }

    fn get_def_mut<'a>(&self, ctx: &'a Context) -> RefMut<'a, Def> {
        match self {
            Self::OpResult { op, res_idx } => {
                let op = op.deref_mut(ctx);
                RefMut::map(op, |opref| &mut opref.get_result_mut(*res_idx).unwrap().def)
            }
            Self::BlockArgument { block, arg_idx } => {
                let block = block.deref_mut(ctx);
                RefMut::map(block, |blockref| {
                    &mut blockref.get_argument_mut(*arg_idx).unwrap().def
                })
            }
        }
    }

    fn get_use_operand<'a>(
        &self,
        ctx: &'a Context,
        descr: &UseDescr,
    ) -> Option<Ref<'a, Operand<ValDefDescr>>> {
        assert!(
            self.get_def(ctx).uses.contains(descr),
            "This UseDescr is not a Use of this Def"
        );
        let op = descr.op.deref(ctx);
        Ref::filter_map(op, |opref| opref.get_operand(descr.opd_idx)).ok()
    }

    fn get_use_operand_mut<'a>(
        &self,
        ctx: &'a Context,
        descr: &UseDescr,
    ) -> Option<RefMut<'a, Operand<ValDefDescr>>> {
        assert!(
            self.get_def(ctx).uses.contains(descr),
            "This UseDescr is not a Use of this Def"
        );
        let op = descr.op.deref_mut(ctx);
        RefMut::filter_map(op, |opref| opref.get_operand_mut(descr.opd_idx)).ok()
    }
}

/// Pointer to / describes a basic block definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BlockDefDescr {
    pub(crate) block: Ptr<BasicBlock>,
}
impl DefDescrTrait for BlockDefDescr {
    fn get_def<'a>(&self, ctx: &'a Context) -> Ref<'a, Def> {
        let block = self.block.deref(ctx);
        Ref::map(block, |blockref| &blockref.preds)
    }

    fn get_def_mut<'a>(&self, ctx: &'a Context) -> RefMut<'a, Def> {
        let block = self.block.deref_mut(ctx);
        RefMut::map(block, |blockref| &mut blockref.preds)
    }

    fn get_use_operand<'a>(
        &self,
        ctx: &'a Context,
        descr: &UseDescr,
    ) -> Option<Ref<'a, Operand<BlockDefDescr>>> {
        assert!(
            self.get_def(ctx).uses.contains(descr),
            "This UseDescr is not a Use of this Def"
        );
        let op = descr.op.deref(ctx);
        Ref::filter_map(op, |opref| opref.get_successor(descr.opd_idx)).ok()
    }

    fn get_use_operand_mut<'a>(
        &self,
        ctx: &'a Context,
        descr: &UseDescr,
    ) -> Option<RefMut<'a, Operand<BlockDefDescr>>> {
        assert!(
            self.get_def(ctx).uses.contains(descr),
            "This UseDescr is not a Use of this Def"
        );
        let op = descr.op.deref_mut(ctx);
        RefMut::filter_map(op, |opref| opref.get_successor_mut(descr.opd_idx)).ok()
    }
}

/// Pointer to / describes a definition.
#[derive(Clone, Copy, Debug)]
pub struct DefDescr<T: DefDescrTrait>(pub(crate) T);

/// A use is a pointer to its definition.
#[derive(Clone, Copy, Debug)]
pub struct Use<Of: DefDescrTrait> {
    /// The definition that this is a use of.
    pub(crate) def: DefDescr<Of>,
}

/// Pointer to / describes a use.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct UseDescr {
    /// Uses of a def can only be in an operation.
    pub(crate) op: Ptr<Operation>,
    /// Used as the i'th operand of op.
    pub(crate) opd_idx: usize,
}
