use combine::{token, Parser};
use pliron_derive::def_op;
use thiserror::Error;

use crate::{
    attribute::{attr_cast, AttrObj},
    basic_block::BasicBlock,
    common_traits::{Named, Verify},
    context::{Context, Ptr},
    dialect::Dialect,
    dialects::builtin::op_interfaces::ZeroResultInterface,
    error::Result,
    identifier::Identifier,
    impl_op_interface, input_err,
    irfmt::{
        parsers::{attr_parser, process_parsed_ssa_defs, spaced, type_parser},
        printers::{attr, concat, region, symb_op_header, typed_symb_op_header},
    },
    linked_list::ContainsLinkedList,
    location::{Located, Location},
    op::{Op, OpObj},
    operation::Operation,
    parsable::{IntoParseResult, Parsable, ParseResult, StateStream},
    printable::{self, Printable},
    r#type::{TypeObj, Typed},
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
#[def_op("builtin.module")]
pub struct ModuleOp {}

impl Printable for ModuleOp {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        symb_op_header(self).fmt(ctx, state, f)?;
        write!(f, " ")?;
        region(self).fmt(ctx, state, f)?;
        Ok(())
    }
}

impl Parsable for ModuleOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        if !results.is_empty() {
            input_err!(
                state_stream.loc(),
                op_interfaces::ZeroResultVerifyErr(Self::get_opid_static().to_string())
            )?
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
            .into()
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

/// An operation with a name containing a single SSA control-flow-graph region.
/// See MLIR's [func.func](https://mlir.llvm.org/docs/Dialects/Func/#funcfunc-mlirfuncfuncop).
///
/// Attributes:
///
/// | key | value |
/// |-----|-------|
/// | [ATTR_KEY_SYM_NAME](super::ATTR_KEY_SYM_NAME) | [StringAttr](super::attributes::StringAttr) |
/// | [ATTR_KEY_FUNC_TYPE](FuncOp::ATTR_KEY_FUNC_TYPE) | [TypeAttr](super::attributes::TypeAttr) |
#[def_op("builtin.func")]
pub struct FuncOp {}

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
        let arg_types = {
            let fn_tyref = ty.deref(ctx);
            let fn_ty = fn_tyref.downcast_ref::<FunctionType>().unwrap();
            fn_ty.get_inputs().clone()
        };
        let region = op.deref_mut(ctx).get_region(0).unwrap();
        let body = BasicBlock::new(ctx, Some("entry".into()), arg_types);
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

impl Typed for FuncOp {
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.get_type(ctx)
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
        typed_symb_op_header(self).fmt(ctx, state, f)?;
        write!(f, " ")?;
        region(self).fmt(ctx, state, f)?;
        Ok(())
    }
}

impl Parsable for FuncOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        if !results.is_empty() {
            input_err!(
                state_stream.loc(),
                op_interfaces::ZeroResultVerifyErr(Self::get_opid_static().to_string())
            )?
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
            .into()
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
        let op = &*self.get_operation().deref(ctx);
        let ty = self.get_type(ctx);
        if !(ty.deref(ctx).is::<FunctionType>()) {
            return verify_err!(op.loc(), FuncOpVerifyErr::NotFuncType);
        }

        if op.get_num_results() != 0 || op.get_num_operands() != 0 {
            return verify_err!(op.loc(), FuncOpVerifyErr::IncorrectNumResultsOpds);
        }
        Ok(())
    }
}

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
#[def_op("builtin.constant")]
pub struct ConstantOp {}

impl ConstantOp {
    /// Attribute key for the constant value.
    pub const ATTR_KEY_VALUE: &'static str = "constant.value";
    /// Get the constant value that this Op defines.
    pub fn get_value(&self, ctx: &Context) -> AttrObj {
        let op = self.get_operation().deref(ctx);
        op.attributes.get(Self::ATTR_KEY_VALUE).unwrap().clone()
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
        state: &printable::State,
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
            input_err!(loc, OneResultVerifyErr(Self::get_opid_static().to_string()))?
        }

        let attr = attr_parser().parse_stream(state_stream).into_result()?.0;

        let op = Box::new(Self::new_unlinked(state_stream.state.ctx, attr));
        process_parsed_ssa_defs(state_stream, &results, op.get_operation())?;

        Ok(op as OpObj).into_parse_result()
    }
}

#[derive(Error, Debug)]
#[error("{}: Unexpected type", ConstantOp::get_opid_static())]
pub struct ConstantOpVerifyErr;

impl Verify for ConstantOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.get_operation().deref(ctx).loc();
        let value = self.get_value(ctx);
        if !(value.is::<IntegerAttr>() || value.is::<FloatAttr>()) {
            return verify_err!(loc, ConstantOpVerifyErr);
        }
        Ok(())
    }
}

impl_op_interface! (ZeroOpdInterface for ConstantOp {});
impl_op_interface! (OneResultInterface for ConstantOp {});

/// A placeholder during parsing to refer to yet undefined operations.
/// MLIR [uses](https://github.com/llvm/llvm-project/blob/185b81e034ba60081023b6e59504dfffb560f3e3/mlir/lib/AsmParser/Parser.cpp#L1075)
/// [UnrealizedConversionCastOp](https://mlir.llvm.org/docs/Dialects/Builtin/#builtinunrealized_conversion_cast-unrealizedconversioncastop)
/// for this purpose.
#[def_op("builtin.forward_ref")]
pub struct ForwardRefOp {}

impl Printable for ForwardRefOp {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.get_opid().fmt(ctx, state, f)?;
        Ok(())
    }
}

impl_op_interface! (OneResultInterface for ForwardRefOp {});
impl_op_interface! (ZeroOpdInterface for ForwardRefOp {});

#[derive(Error, Debug)]
#[error("{0} is a temporary Op during parsing. It must not exit in a well-formed program.")]
pub struct ForwardRefOpExistenceErr(String);

impl Verify for ForwardRefOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        verify_err!(
            self.get_operation().deref(ctx).loc(),
            ForwardRefOpExistenceErr(self.get_result(ctx).unique_name(ctx))
        )
    }
}

impl Parsable for ForwardRefOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _results: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        input_err!(
            state_stream.loc(),
            ForwardRefOpExistenceErr(
                ForwardRefOp::get_opid_static()
                    .disp(state_stream.state.ctx)
                    .to_string()
            )
        )?
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
