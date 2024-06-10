use apint::ApInt;
use pliron::{
    builtin::{
        self,
        attributes::IntegerAttr,
        op_interfaces::{IsTerminatorInterface, OneResultInterface, ZeroResultVerifyErr},
        ops::{ConstantOp, FuncOp, ModuleOp},
        types::{FunctionType, IntegerType, Signedness},
    },
    common_traits::Verify,
    context::Context,
    debug_info::set_operation_result_name,
    dialect::{Dialect, DialectName},
    identifier::Identifier,
    impl_op_interface, impl_verify_succ, input_err,
    irfmt::parsers::ssa_opd_parser,
    location::{Located, Location},
    op::{Op, OpObj},
    operation::Operation,
    parsable::{self, Parsable, ParseResult},
    printable::{self, Printable},
    result::Result,
    use_def_lists::Value,
};
use pliron_derive::def_op;

#[def_op("test.return")]
pub struct ReturnOp {}
impl ReturnOp {
    pub fn new(ctx: &mut Context, value: Value) -> Self {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![value], vec![], 0);
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
                .get_operand(0)
                .unwrap()
                .disp(ctx)
        )
    }
}
impl Parsable for ReturnOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;
    fn parse<'a>(
        state_stream: &mut parsable::StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        if !results.is_empty() {
            input_err!(
                state_stream.loc(),
                ZeroResultVerifyErr(Self::get_opid_static().to_string())
            )?
        }

        ssa_opd_parser()
            .parse_stream(state_stream)
            .map(|opd| -> OpObj { Box::new(Self::new(state_stream.state.ctx, opd)) })
            .into()
    }
}

impl_op_interface!(IsTerminatorInterface for ReturnOp {});
impl_verify_succ!(ReturnOp);

pub fn setup_context_dialects() -> Context {
    let mut ctx = Context::new();
    builtin::register(&mut ctx);
    // Create a test dialect for test ops/attributes and types.
    let test_dialect = Dialect::new(DialectName::new("test"));
    test_dialect.register(&mut ctx);
    ReturnOp::register(&mut ctx, ReturnOp::parser_fn);
    ctx
}

// Create a print a module "bar", with a function "foo"
// containing a single `return 0`.
pub fn const_ret_in_mod(ctx: &mut Context) -> Result<(ModuleOp, FuncOp, ConstantOp, ReturnOp)> {
    let i64_ty = IntegerType::get(ctx, 64, Signedness::Signed);
    let module = ModuleOp::new(ctx, "bar");
    // Our function is going to have type () -> ().
    let func_ty = FunctionType::get(ctx, vec![], vec![i64_ty.into()]);
    let func = FuncOp::new(ctx, "foo", func_ty);
    module.add_operation(ctx, func.get_operation());
    let bb = func.get_entry_block(ctx);

    // Create a `const 0` op and add it to bb.
    let zero_const = IntegerAttr::new(i64_ty, ApInt::from(0));
    let const_op = ConstantOp::new(ctx, zero_const.into());
    const_op.get_operation().insert_at_front(bb, ctx);
    set_operation_result_name(ctx, const_op.get_operation(), 0, "c0".to_string());

    // Return the constant.
    let ret_op = ReturnOp::new(ctx, const_op.get_result(ctx));
    ret_op.get_operation().insert_at_back(bb, ctx);

    module.get_operation().verify(ctx)?;

    Ok((module, func, const_op, ret_op))
}
