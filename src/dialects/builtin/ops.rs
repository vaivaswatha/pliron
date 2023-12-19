use combine::{easy::ParseError, token, ParseResult, Parser, Positioned};
use thiserror::Error;

use crate::{
    attribute::{self, attr_cast, attr_parser, AttrObj},
    basic_block::BasicBlock,
    common_traits::{Named, Verify},
    context::{Context, Ptr},
    debug_info::set_operation_result_name,
    declare_op,
    dialect::Dialect,
    dialects::builtin::op_interfaces::ZeroResultInterface,
    error::Result,
    identifier::Identifier,
    impl_op_interface, input_err,
    linked_list::ContainsLinkedList,
    op::{Op, OpObj},
    operation::Operation,
    parsable::{spaced, to_parse_result, Parsable, StateStream},
    printable::{self, Printable},
    r#type::{type_parser, TypeObj},
    region::Region,
    verify_err,
};

use super::{
    attr_interfaces::TypedAttrInterface,
    attributes::{FloatAttr, IntegerAttr, TypeAttr},
    op_interfaces::{
        self, IsolatedFromAboveInterface, OneRegionInterface, OneResultInterface,
        OneResultVerifyErr, SingleBlockRegionInterface, SymbolOpInterface, ZeroOpdInterface,
    },
    types::{FunctionType, UnitType},
};

declare_op!(
    /// Represents a module, a top level container operation.
    ///
    /// See MLIR's [builtin.module](https://mlir.llvm.org/docs/Dialects/Builtin/#builtinmodule-mlirmoduleop).
    /// It contains a single [SSACFG](super::op_interfaces::RegionKind::SSACFG)
    /// region containing a single block which can contain any operations and
    /// does not have a terminator.
    ///
    /// Attributes:
    ///
    /// | key | value |
    /// |-----|-------|
    /// | [ATTR_KEY_SYM_NAME](super::ATTR_KEY_SYM_NAME) | [StringAttr](super::attributes::StringAttr) |
    ModuleOp,
    "module",
    "builtin"
);

impl Printable for ModuleOp {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(
            f,
            "{} @{} ",
            self.get_opid().disp(ctx),
            self.get_symbol_name(ctx),
        )?;
        self.get_region(ctx).fmt(ctx, state, f)?;
        Ok(())
    }
}

impl Parsable for ModuleOp {
    type Arg = Vec<Identifier>;
    type Parsed = OpObj;
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<Self::Parsed, ParseError<StateStream<'a>>> {
        if !results.is_empty() {
            return to_parse_result(
                input_err!(op_interfaces::ZeroResultVerifyErr(
                    Self::get_opid_static().to_string()
                )),
                state_stream.position(),
            );
        }
        let op = Operation::new(
            state_stream.state.ctx,
            Self::get_opid_static(),
            vec![],
            vec![],
            0,
        );
        let mut parser =
            spaced(token('@').with(Identifier::parser(()))).and(spaced(Region::parser(op)));
        parser
            .parse_stream(state_stream)
            .map(|(name, _region)| -> OpObj {
                let op = Box::new(ModuleOp { op });
                op.set_symbol_name(state_stream.state.ctx, &name);
                op
            })
    }
}

impl Verify for ModuleOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

impl ModuleOp {
    /// Create a new [ModuleOp].
    /// The underlying [Operation] is not linked to a [BasicBlock].
    /// The returned module has a single [crate::region::Region] with a single (BasicBlock)[crate::basic_block::BasicBlock].
    pub fn new(ctx: &mut Context, name: &str) -> ModuleOp {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], 1);
        let opop = ModuleOp { op };
        opop.set_symbol_name(ctx, name);

        // Create an empty block.
        let region = op.deref_mut(ctx).get_region(0).unwrap();
        let block = BasicBlock::new(ctx, None, vec![]);
        block.insert_at_front(region, ctx);

        opop
    }

    /// Add an [Operation] into this module.
    pub fn add_operation(&self, ctx: &mut Context, op: Ptr<Operation>) {
        self.append_operation(ctx, op, 0)
    }
}

impl_op_interface!(OneRegionInterface for ModuleOp {});
impl_op_interface!(SingleBlockRegionInterface for ModuleOp {});
impl_op_interface!(SymbolOpInterface for ModuleOp {});
impl_op_interface!(IsolatedFromAboveInterface for ModuleOp {});
impl_op_interface!(ZeroOpdInterface for ModuleOp {});
impl_op_interface!(ZeroResultInterface for ModuleOp {});

declare_op!(
    /// An operation with a name containing a single SSA control-flow-graph region.
    /// See MLIR's [func.func](https://mlir.llvm.org/docs/Dialects/Func/#funcfunc-mlirfuncfuncop).
    ///
    /// Attributes:
    ///
    /// | key | value |
    /// |-----|-------|
    /// | [ATTR_KEY_SYM_NAME](super::ATTR_KEY_SYM_NAME) | [StringAttr](super::attributes::StringAttr) |
    /// | [ATTR_KEY_FUNC_TYPE](FuncOp::ATTR_KEY_FUNC_TYPE) | [TypeAttr](super::attributes::TypeAttr) |
    FuncOp,
    "func",
    "builtin"
);

impl FuncOp {
    /// Attribute key for the constant value.
    pub const ATTR_KEY_FUNC_TYPE: &'static str = "func.type";

    /// Create a new [FuncOp].
    /// The underlying [Operation] is not linked to a [BasicBlock].
    /// The returned function has a single region with an empty `entry` block.
    pub fn new_unlinked(ctx: &mut Context, name: &str, ty: Ptr<TypeObj>) -> FuncOp {
        let ty_attr = TypeAttr::create(ty);
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], 1);

        // Create an empty entry block.
        let region = op.deref_mut(ctx).get_region(0).unwrap();
        let body = BasicBlock::new(ctx, Some("entry".into()), vec![]);
        body.insert_at_front(region, ctx);
        {
            let opref = &mut *op.deref_mut(ctx);
            // Set function type attributes.
            opref.attributes.insert(Self::ATTR_KEY_FUNC_TYPE, ty_attr);
        }
        let opop = FuncOp { op };
        opop.set_symbol_name(ctx, name);

        opop
    }

    /// Get the function signature (type).
    pub fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        let opref = self.get_operation().deref(ctx);
        let ty_attr = opref.attributes.get(Self::ATTR_KEY_FUNC_TYPE).unwrap();
        attr_cast::<dyn TypedAttrInterface>(&**ty_attr)
            .unwrap()
            .get_type()
    }

    /// Get the entry block of this function.
    pub fn get_entry_block(&self, ctx: &Context) -> Ptr<BasicBlock> {
        self.get_region(ctx).deref(ctx).get_head().unwrap()
    }

    /// Get an iterator over all operations.
    pub fn op_iter<'a>(&self, ctx: &'a Context) -> impl Iterator<Item = Ptr<Operation>> + 'a {
        self.get_region(ctx)
            .deref(ctx)
            .iter(ctx)
            .flat_map(|bb| bb.deref(ctx).iter(ctx))
    }
}

impl_op_interface!(OneRegionInterface for FuncOp {});
impl_op_interface!(SymbolOpInterface for FuncOp {});
impl_op_interface!(IsolatedFromAboveInterface for FuncOp {});

impl Printable for FuncOp {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(
            f,
            "{} @{}: {} ",
            self.get_opid().disp(ctx),
            self.get_symbol_name(ctx),
            self.get_type(ctx).disp(ctx),
        )?;
        self.get_region(ctx).fmt(ctx, state, f)?;
        Ok(())
    }
}

impl Parsable for FuncOp {
    type Arg = Vec<Identifier>;
    type Parsed = OpObj;
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<Self::Parsed, ParseError<StateStream<'a>>> {
        if !results.is_empty() {
            return to_parse_result(
                input_err!(op_interfaces::ZeroResultVerifyErr(
                    Self::get_opid_static().to_string()
                )),
                state_stream.position(),
            );
        }

        let op = Operation::new(
            state_stream.state.ctx,
            Self::get_opid_static(),
            vec![],
            vec![],
            0,
        );

        let mut parser = (
            spaced(token('@').with(Identifier::parser(()))).skip(spaced(token(':'))),
            spaced(type_parser()),
            spaced(Region::parser(op)),
        );

        // Parse and build the function, providing name and type details.
        parser
            .parse_stream(state_stream)
            .map(|(fname, fty, _region)| -> OpObj {
                let ctx = &mut state_stream.state.ctx;
                {
                    let ty_attr = TypeAttr::create(fty);
                    let opref = &mut *op.deref_mut(ctx);
                    // Set function type attributes.
                    opref.attributes.insert(Self::ATTR_KEY_FUNC_TYPE, ty_attr);
                }
                let opop = Box::new(FuncOp { op });
                opop.set_symbol_name(ctx, &fname);
                opop
            })
    }
}

#[derive(Error, Debug)]
pub enum FuncOpVerifyErr {
    #[error("function does not have function type")]
    NotFuncType,
    #[error("incorrect number of results or operands")]
    IncorrectNumResultsOpds,
}

impl Verify for FuncOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let ty = self.get_type(ctx);
        if !(ty.deref(ctx).is::<FunctionType>()) {
            return verify_err!(FuncOpVerifyErr::NotFuncType);
        }
        let op = &*self.get_operation().deref(ctx);
        if op.get_num_results() != 0 || op.get_num_operands() != 0 {
            return verify_err!(FuncOpVerifyErr::IncorrectNumResultsOpds);
        }
        Ok(())
    }
}

declare_op!(
    /// Numeric constant.
    /// See MLIR's [arith.constant](https://mlir.llvm.org/docs/Dialects/ArithOps/#arithconstant-mlirarithconstantop).
    ///
    /// Attributes:
    ///
    /// | key | value |
    /// |-----|-------|
    /// |[ATTR_KEY_VALUE](ConstantOp::ATTR_KEY_VALUE) | [IntegerAttr] or [FloatAttr] |
    ///
    /// Results:
    ///
    /// | result | description |
    /// |-----|-------|
    /// | `result` | any type |
    ConstantOp,
    "constant",
    "builtin"
);

impl ConstantOp {
    /// Attribute key for the constant value.
    pub const ATTR_KEY_VALUE: &'static str = "constant.value";
    /// Get the constant value that this Op defines.
    pub fn get_value(&self, ctx: &Context) -> AttrObj {
        let op = self.get_operation().deref(ctx);
        let value = op.attributes.get(Self::ATTR_KEY_VALUE).unwrap();
        if value.is::<IntegerAttr>() {
            attribute::clone::<IntegerAttr>(value)
        } else {
            attribute::clone::<FloatAttr>(value)
        }
    }

    /// Create a new [ConstantOp]. The underlying [Operation] is not linked to a [BasicBlock].
    pub fn new_unlinked(ctx: &mut Context, value: AttrObj) -> ConstantOp {
        let result_type = attr_cast::<dyn TypedAttrInterface>(&*value)
            .expect("ConstantOp const value must provide TypedAttrInterface")
            .get_type();
        let op = Operation::new(ctx, Self::get_opid_static(), vec![result_type], vec![], 0);
        op.deref_mut(ctx)
            .attributes
            .insert(Self::ATTR_KEY_VALUE, value);
        ConstantOp { op }
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
            self.get_result(ctx).unique_name(ctx),
            self.get_opid().disp(ctx),
            self.get_value(ctx).disp(ctx)
        )
    }
}

impl Parsable for ConstantOp {
    type Arg = Vec<Identifier>;
    type Parsed = OpObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<Self::Parsed, ParseError<StateStream<'a>>> {
        let position = state_stream.position();

        if results.len() != 1 {
            return to_parse_result(
                input_err!(OneResultVerifyErr(Self::get_opid_static().to_string())),
                position,
            );
        }

        attr_parser()
            .parse_stream(state_stream)
            .and_then(|attr| -> ParseResult<OpObj, _> {
                let op = Box::new(Self::new_unlinked(state_stream.state.ctx, attr));
                if let Err(err) = state_stream.state.name_tracker.ssa_def(
                    state_stream.state.ctx,
                    &results[0],
                    op.get_result(state_stream.state.ctx),
                ) {
                    return to_parse_result(Err(err), position);
                }
                set_operation_result_name(
                    state_stream.state.ctx,
                    op.get_operation(),
                    0,
                    results[0].to_string(),
                );
                to_parse_result(Ok(op), position)
            })
    }
}

#[derive(Error, Debug)]
#[error("{}: Unexpected type", ConstantOp::get_opid_static())]
pub struct ConstantOpVerifyErr;

impl Verify for ConstantOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let value = self.get_value(ctx);
        if !(value.is::<IntegerAttr>() || value.is::<FloatAttr>()) {
            return verify_err!(ConstantOpVerifyErr);
        }
        Ok(())
    }
}

impl_op_interface! (ZeroOpdInterface for ConstantOp {});
impl_op_interface! (OneResultInterface for ConstantOp {});

declare_op!(
    /// A placeholder during parsing to refer to yet undefined operations.
    /// MLIR [uses](https://github.com/llvm/llvm-project/blob/185b81e034ba60081023b6e59504dfffb560f3e3/mlir/lib/AsmParser/Parser.cpp#L1075)
    /// [UnrealizedConversionCastOp](https://mlir.llvm.org/docs/Dialects/Builtin/#builtinunrealized_conversion_cast-unrealizedconversioncastop)
    /// for this purpose.
    ForwardRefOp,
    "forward_ref",
    "builtin"
);

impl Printable for ForwardRefOp {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "{} = {}",
            self.get_result(ctx).unique_name(ctx),
            self.get_opid().disp(ctx),
        )
    }
}

impl_op_interface! (OneResultInterface for ForwardRefOp {});
impl_op_interface! (ZeroOpdInterface for ForwardRefOp {});

#[derive(Error, Debug)]
#[error("{0} is a temporary Op during parsing. It must not exit in a well-formed program.")]
pub struct ForwardRefOpExistenceErr(String);

impl Verify for ForwardRefOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        verify_err!(ForwardRefOpExistenceErr(
            self.get_result(ctx).unique_name(ctx)
        ))
    }
}

impl Parsable for ForwardRefOp {
    type Arg = Vec<Identifier>;
    type Parsed = OpObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _results: Self::Arg,
    ) -> ParseResult<Self::Parsed, ParseError<StateStream<'a>>> {
        to_parse_result(
            input_err!(ForwardRefOpExistenceErr(
                ForwardRefOp::get_opid_static()
                    .disp(state_stream.state.ctx)
                    .to_string()
            )),
            state_stream.stream.position(),
        )
    }
}

impl ForwardRefOp {
    /// Create a new [ForwardRefOp].
    /// The underlying [Operation] is not linked to a [BasicBlock].
    pub fn new_unlinked(ctx: &mut Context) -> ForwardRefOp {
        let ty = UnitType::get(ctx);
        let op = Operation::new(ctx, Self::get_opid_static(), vec![ty], vec![], 0);
        ForwardRefOp { op }
    }
}

pub fn register(ctx: &mut Context, dialect: &mut Dialect) {
    ModuleOp::register(ctx, dialect, ModuleOp::parser_fn);
    FuncOp::register(ctx, dialect, FuncOp::parser_fn);
    ConstantOp::register(ctx, dialect, ConstantOp::parser_fn);
    ForwardRefOp::register(ctx, dialect, ForwardRefOp::parser_fn);
}
