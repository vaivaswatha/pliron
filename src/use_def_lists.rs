use std::cell::{Ref, RefMut};

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    operation::{Operand, Operation},
    value::Value,
};

/// A reference to the definition of a [Value].
#[derive(Clone, Copy, Debug)]
pub enum DefDescr {
    OpResult {
        op: Ptr<Operation>,
        res_idx: usize,
    },
    BlockArgument {
        block: Ptr<BasicBlock>,
        arg_idx: usize,
    },
}

impl DefDescr {
    pub fn get_value_ref<'a>(&'a self, ctx: &'a Context) -> Ref<'a, dyn Value> {
        match self {
            Self::OpResult { op, res_idx } => {
                let op = op.deref(ctx);
                Ref::map(op, |opref| opref.get_result(*res_idx).unwrap())
            }
            Self::BlockArgument {
                block: _,
                arg_idx: _,
            } => {
                todo!()
            }
        }
    }
    pub fn get_value_ref_mut<'a>(&'a self, ctx: &'a Context) -> RefMut<'a, dyn Value> {
        match self {
            Self::OpResult { op, res_idx } => {
                let op = op.deref_mut(ctx);
                RefMut::map(op, |opref| opref.get_result_mut(*res_idx).unwrap())
            }
            Self::BlockArgument {
                block: _,
                arg_idx: _,
            } => {
                todo!()
            }
        }
    }
}

/// A use is a reference to its definition.
#[derive(Clone, Copy, Debug)]
pub struct Use {
    /// Operation result or block argument.
    pub def: DefDescr,
    /// Index in the def's @uses list.
    pub use_idx: usize,
}

///  A reference to the use of a [Value].
#[derive(Clone, Copy, Debug)]
pub struct UseDescr {
    /// Uses of a def can only be in an operation.
    pub op: Ptr<Operation>,
    /// Used as the i'th operand of op.
    pub opd_idx: usize,
}

impl UseDescr {
    pub fn get_operand<'a>(&self, ctx: &'a Context) -> Ref<'a, Operand> {
        let op = self.op.deref(ctx);
        Ref::map(op, |opref| opref.get_operand(self.opd_idx).unwrap())
    }
    pub fn get_operand_mut<'a>(&self, ctx: &'a Context) -> RefMut<'a, Operand> {
        let op = self.op.deref_mut(ctx);
        RefMut::map(op, |opref| opref.get_operand_mut(self.opd_idx).unwrap())
    }
}

/// A def is a list of its uses.
#[derive(Debug)]
pub struct Def {
    /// The list of uses of this Def.
    pub uses: Vec<UseDescr>,
}
