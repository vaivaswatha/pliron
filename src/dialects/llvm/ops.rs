use crate::{
    common_traits::{Stringable, Verify},
    context::{Context, Ptr},
    dialects::builtin::properties::IsTerminator,
    error::CompilerError,
    op::Op,
    operation::Operation,
};

/// Equivalent to LLVM's return opcode.
#[derive(Clone, Copy)]
struct ReturnOp {
    op: Ptr<Operation>,
}

impl Op for ReturnOp {
    fn get_operation(&self) -> Ptr<Operation> {
        self.op
    }

    fn new(op: Ptr<Operation>) -> ReturnOp {
        ReturnOp { op }
    }
}

impl Stringable for ReturnOp {
    fn to_string(&self, _ctx: &Context) -> String {
        todo!()
    }
}

impl Verify for ReturnOp {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

impl IsTerminator for ReturnOp {
    fn is_terminator(&self) -> bool {
        true
    }
}
