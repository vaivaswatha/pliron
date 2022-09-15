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

use std::cell::{Ref, RefMut};

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    operation::Operation,
    vec_exns::VecExtns,
};

/// A definition is a list of its uses.
#[derive(Debug)]
pub struct Def {
    /// The list of uses of this Def.
    uses: Vec<UseDescr>,
}

impl Def {
    /// Adds r#use as a use of self and returns the use index.
    fn add_use(&mut self, r#use: UseDescr) -> usize {
        self.uses.push_back(r#use)
    }
    /// Create a new definition.
    pub(crate) fn new() -> Def {
        Def { uses: vec![] }
    }

    /// Get a descriptor to the i'th use of this Def.
    pub(crate) fn get_use(&self, i: usize) -> Option<UseDescr> {
        self.uses.get(i).cloned()
    }

    /// Get the number of uses of this Def.
    pub(crate) fn num_uses(&self) -> usize {
        self.uses.len()
    }
}

/// Description of a definition.
pub trait DefDescrTrait: Copy {
    /// Get a reference to the underlying Def.
    fn get_def<'a>(&self, ctx: &'a Context) -> Ref<'a, Def>;
    /// Get a mutable reference to the underlying Def.
    fn get_def_mut<'a>(&self, ctx: &'a Context) -> RefMut<'a, Def>;
    /// Get a reference to the i'th use of the [Def] described by self.
    fn get_resolved_use<'a>(&self, ctx: &'a Context, i: usize) -> Option<Ref<'a, Use<Self>>>;
    /// Get a mutable reference to the i'th use of the [Def] described by self.
    fn get_resolved_use_mut<'a>(&self, ctx: &'a Context, i: usize)
        -> Option<RefMut<'a, Use<Self>>>;

    /// Get a descriptor to the i'th use of the [Def] described by self.
    fn get_use(&self, ctx: &Context, i: usize) -> Option<UseDescr> {
        self.get_def(ctx).get_use(i)
    }

    /// How many uses does the [Def] corresponding to this [DefDescr] have?
    fn num_uses(&self, ctx: &Context) -> usize {
        self.get_def(ctx).num_uses()
    }

    /// This definition has a new use. Track it and return a corresponding [Use].
    /// The returned [Use] is to be used in constructing an operand etc.
    fn add_use(&self, ctx: &Context, r#use: UseDescr) -> Use<Self>
    where
        Self: Sized,
    {
        let use_idx = self.get_def_mut(ctx).add_use(r#use);
        Use {
            def: DefDescr::<Self>(*self),
            use_idx,
        }
    }

    /// Replace all uses of `self` with `other`.
    fn replace_all_uses_with(&self, ctx: &Context, other: &Self) {
        let def = self.get_def(ctx);
        for use_i in 0..def.uses.len() {
            let mut r#use = self.get_resolved_use_mut(ctx, use_i).unwrap();
            *r#use = other.add_use(ctx, def.uses[use_i])
        }
        // self will no longer have any uses.
        self.get_def_mut(ctx).uses.clear();
    }
}

/// Pointer to / describes a value definition.
#[derive(Clone, Copy, Debug)]
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

    fn get_resolved_use<'a>(
        &self,
        ctx: &'a Context,
        i: usize,
    ) -> Option<Ref<'a, Use<ValDefDescr>>> {
        let def = self.get_def(ctx);
        let descr = def.uses.get(i)?;
        let op = descr.op.deref(ctx);
        Some(Ref::map(op, |opref| {
            &opref.get_operand(descr.opd_idx).unwrap().r#use
        }))
    }

    fn get_resolved_use_mut<'a>(
        &self,
        ctx: &'a Context,
        i: usize,
    ) -> Option<RefMut<'a, Use<ValDefDescr>>> {
        let def = self.get_def(ctx);
        let descr = def.uses.get(i)?;
        let op = descr.op.deref_mut(ctx);
        Some(RefMut::map(op, |opref| {
            &mut opref.get_operand_mut(descr.opd_idx).unwrap().r#use
        }))
    }
}

/// Pointer to / describes a basic block definition.
#[derive(Clone, Copy, Debug)]
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

    fn get_resolved_use<'a>(
        &self,
        ctx: &'a Context,
        i: usize,
    ) -> Option<Ref<'a, Use<BlockDefDescr>>> {
        let def = self.get_def(ctx);
        let descr = def.uses.get(i)?;
        let op = descr.op.deref(ctx);
        Some(Ref::map(op, |opref| {
            &opref.get_successor(descr.opd_idx).unwrap().r#use
        }))
    }

    fn get_resolved_use_mut<'a>(
        &self,
        ctx: &'a Context,
        i: usize,
    ) -> Option<RefMut<'a, Use<BlockDefDescr>>> {
        let def = self.get_def(ctx);
        let descr = def.uses.get(i)?;
        let op = descr.op.deref_mut(ctx);
        Some(RefMut::map(op, |opref| {
            &mut opref.get_successor_mut(descr.opd_idx).unwrap().r#use
        }))
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
    /// Index in the def's @uses list.
    pub(crate) use_idx: usize,
}

/// Pointer to / describes a use.
#[derive(Clone, Copy, Debug)]
pub struct UseDescr {
    /// Uses of a def can only be in an operation.
    pub(crate) op: Ptr<Operation>,
    /// Used as the i'th operand of op.
    pub(crate) opd_idx: usize,
}
