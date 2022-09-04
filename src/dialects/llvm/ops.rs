use crate::{
    common_traits::{Stringable, Verify},
    context::{Context, Ptr},
    dialect::{Dialect, DialectName},
    dialects::builtin::properties::IsTerminator,
    error::CompilerError,
    op::{Op, OpId, OpName},
    operation::Operation,
};

/// Equivalent to LLVM's return opcode.
#[derive(Clone, Copy)]
pub struct ReturnOp {
    op: Ptr<Operation>,
}

impl Op for ReturnOp {
    fn get_operation(&self) -> Ptr<Operation> {
        self.op
    }

    fn create(op: Ptr<Operation>) -> Box<dyn Op> {
        Box::new(ReturnOp { op })
    }

    fn get_opid(&self) -> OpId {
        Self::get_opid_static()
    }

    fn get_opid_static() -> OpId {
        OpId {
            name: OpName::new("ReturnOp"),
            dialect: DialectName::new("llvm"),
        }
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

pub fn register(ctx: &mut Context, dialect: &mut Dialect) {
    ReturnOp::register(ctx, dialect);
}
