use crate::{
    basic_block::{BasicBlock},
    context::Ptr,
    operation::Operation,
};

// A reference to the definition of a value.
#[derive(Clone, Copy)]
pub enum DefRef {
    OpResult {
        op: Ptr<Operation>,
        res_idx: usize
    },
    BlockArgument {
        block: Ptr<BasicBlock>,
        arg_idx: usize,
    },
}

// A use is a reference to its definition.
#[derive(Clone, Copy)]
pub struct Use {
    // Operation result or block argument.
    pub def: DefRef,
    // Index in the def's @uses list.
    pub use_idx: usize,
}

//  A reference to the use of a value.
#[derive(Clone, Copy)]
pub struct UseRef {
    // Uses of a def can only be in an operation.
    pub op: Ptr<Operation>,
    // Used as the i'th operand of op.
    pub opd_idx: usize,
}

// A def is a list of its uses.
pub struct Def {
    pub uses: Vec<UseRef>,
}
