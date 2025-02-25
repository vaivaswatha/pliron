use std::sync::LazyLock;

use awint::bw;
use pliron::derive::{def_op, derive_op_interface_impl};
use pliron::utils::apint::APInt;
use pliron::{
    attribute::AttrObj,
    builtin::{
        self,
        attributes::IntegerAttr,
        op_interfaces::{
            IsTerminatorInterface, OneResultInterface, OneResultVerifyErr,
            SingleBlockRegionInterface, ZeroOpdInterface,
        },
        ops::{FuncOp, ModuleOp},
        types::{FunctionType, IntegerType, Signedness},
    },
    common_traits::Verify,
    context::Context,
    debug_info::set_operation_result_name,
    dialect::{Dialect, DialectName},
    identifier::Identifier,
    impl_verify_succ, input_err,
    irfmt::parsers::{attr_parser, process_parsed_ssa_defs},
    location::{Located, Location},
    op::{Op, OpObj},
    operation::Operation,
    parsable::{IntoParseResult, Parsable, ParseResult, StateStream},
    printable::{self, Printable},
    result::Result,
    value::Value,
};
use pliron_derive::format_op;

#[def_op("test.return")]
#[format_op("$0")]
#[derive_op_interface_impl(IsTerminatorInterface)]
pub struct ReturnOp;
impl ReturnOp {
    pub fn new(ctx: &mut Context, value: Value) -> Self {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![value], vec![], 0);
        ReturnOp { op }
    }
}

impl_verify_succ!(ReturnOp);

#[def_op("test.constant")]
#[derive_op_interface_impl(ZeroOpdInterface, OneResultInterface)]
pub struct ConstantOp;
impl_verify_succ!(ConstantOp);
impl ConstantOp {
    pub const ATTR_KEY_VALUE: LazyLock<Identifier> =
        LazyLock::new(|| "constant_value".try_into().unwrap());

    pub fn new(ctx: &mut Context, value: u64) -> Self {
        let i64_ty = IntegerType::get(ctx, 64, Signedness::Signed);
        let int_attr = IntegerAttr::new(i64_ty, APInt::from_u64(value, bw(64)));
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![i64_ty.into()],
            vec![],
            vec![],
            0,
        );
        op.deref_mut(ctx)
            .attributes
            .0
            .insert(Self::ATTR_KEY_VALUE.clone(), Box::new(int_attr));
        ConstantOp { op }
    }

    pub fn get_value(&self, ctx: &Context) -> AttrObj {
        let op = self.get_operation().deref(ctx);
        op.attributes.0.get(&Self::ATTR_KEY_VALUE).unwrap().clone()
    }
}
impl Printable for ConstantOp {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(
            f,
            "{} = {} {}",
            self.get_result(ctx).disp(ctx),
            self.get_opid().disp(ctx),
            self.get_value(ctx).disp(ctx)
        )
    }
}
impl Parsable for ConstantOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        let loc = state_stream.loc();

        if results.len() != 1 {
            input_err!(
                loc.clone(),
                OneResultVerifyErr(Self::get_opid_static().to_string())
            )?
        }

        let attr = attr_parser().parse_stream(state_stream).into_result()?.0;
        let int_attr = match attr.downcast::<IntegerAttr>() {
            Ok(int_attr) => int_attr,
            Err(attr) => input_err!(
                loc,
                "Expected integer attribute, but found {}",
                attr.disp(state_stream.state.ctx)
            )?,
        };
        let int_val: u64 = Into::<APInt>::into(*int_attr).to_u64();
        let op = Box::new(Self::new(state_stream.state.ctx, int_val));
        process_parsed_ssa_defs(state_stream, &results, op.get_operation())?;

        Ok(op as OpObj).into_parse_result()
    }
}

pub fn setup_context_dialects() -> Context {
    let mut ctx = Context::new();
    builtin::register(&mut ctx);
    // Create a test dialect for test ops/attributes and types.
    let test_dialect = Dialect::new(DialectName::new("test"));
    test_dialect.register(&mut ctx);
    ReturnOp::register(&mut ctx, ReturnOp::parser_fn);
    ConstantOp::register(&mut ctx, ConstantOp::parser_fn);
    ctx
}

// Create a print a module "bar", with a function "foo"
// containing a single `return 0`.
pub fn const_ret_in_mod(ctx: &mut Context) -> Result<(ModuleOp, FuncOp, ConstantOp, ReturnOp)> {
    let i64_ty = IntegerType::get(ctx, 64, Signedness::Signed);
    let module = ModuleOp::new(ctx, &"bar".try_into().unwrap());
    // Our function is going to have type () -> ().
    let func_ty = FunctionType::get(ctx, vec![], vec![i64_ty.into()]);
    let func = FuncOp::new(ctx, &"foo".try_into().unwrap(), func_ty);
    module.append_operation(ctx, func.get_operation(), 0);
    let bb = func.get_entry_block(ctx);

    // Create a `const 0` op and add it to bb.
    let const_op = ConstantOp::new(ctx, 0);
    const_op.get_operation().insert_at_front(bb, ctx);
    set_operation_result_name(ctx, const_op.get_operation(), 0, "c0".try_into().unwrap());

    // Return the constant.
    let ret_op = ReturnOp::new(ctx, const_op.get_result(ctx));
    ret_op.get_operation().insert_at_back(bb, ctx);

    module.get_operation().verify(ctx)?;

    Ok((module, func, const_op, ret_op))
}
