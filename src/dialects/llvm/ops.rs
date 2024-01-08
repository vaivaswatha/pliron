use crate::{
    common_traits::Verify,
    context::Context,
    declare_op,
    dialect::Dialect,
    dialects::builtin::op_interfaces::{IsTerminatorInterface, ZeroResultVerifyErr},
    error::Result,
    identifier::Identifier,
    impl_op_interface, input_err,
    location::{Located, Location},
    op::{Op, OpObj},
    operation::Operation,
    parsable::{Parsable, ParseResult},
    printable::{self, Printable},
    use_def_lists::Value,
};

declare_op!(
    /// Equivalent to LLVM's return opcode.
    ///
    /// Operands:
    ///
    /// | operand | description |
    /// |-----|-------|
    /// | `arg` | any type |
    ReturnOp,
    "return",
    "llvm"
);

impl ReturnOp {
    pub fn new_unlinked(ctx: &mut Context, value: Value) -> ReturnOp {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![value], 0);
        ReturnOp { op }
    }
}

impl Printable for ReturnOp {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(
            f,
            "{} {}",
            self.get_opid().disp(ctx),
            self.get_operation()
                .deref(ctx)
                .get_operand_ref(0)
                .unwrap()
                .disp(ctx)
        )
    }
}

impl Verify for ReturnOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

impl Parsable for ReturnOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;
    fn parse<'a>(
        state_stream: &mut crate::parsable::StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        if !results.is_empty() {
            input_err!(
                state_stream.loc(),
                ZeroResultVerifyErr(Self::get_opid_static().to_string())
            )?
        }

        Identifier::parser(())
            .parse_stream(state_stream)
            .map(|opd| -> OpObj {
                let opd = state_stream
                    .state
                    .name_tracker
                    .ssa_use(state_stream.state.ctx, &opd);
                Box::new(Self::new_unlinked(state_stream.state.ctx, opd))
            })
            .into()
    }
}

impl_op_interface!(IsTerminatorInterface for ReturnOp {});

pub fn register(ctx: &mut Context, dialect: &mut Dialect) {
    ReturnOp::register(ctx, dialect, ReturnOp::parser_fn);
}
