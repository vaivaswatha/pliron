use combine::{Parser, optional, token};
use pliron::derive::{def_op, derive_op_interface_impl};
use pliron_derive::derive_attr_get_set;
use thiserror::Error;

use crate::{
    attribute::{AttributeDict, attr_cast},
    basic_block::BasicBlock,
    builtin::{
        op_interfaces::{ATTR_KEY_SYM_NAME, NoTerminatorInterface, ZeroResultInterface},
        ops::func_op_attr_names::ATTR_KEY_FUNC_TYPE,
        type_interfaces::FunctionTypeInterface,
    },
    common_traits::{Named, Verify},
    context::{Context, Ptr},
    identifier::Identifier,
    impl_verify_succ, indented_block, input_err,
    irfmt::{
        parsers::{spaced, type_parser},
        printers::op::{region, symb_op_header, typed_symb_op_header},
    },
    linked_list::ContainsLinkedList,
    location::{Located, Location},
    op::{Op, OpObj},
    operation::Operation,
    parsable::{Parsable, ParseResult, StateStream},
    printable::{self, Printable, indented_nl},
    region::Region,
    result::Result,
    r#type::{TypeObj, TypePtr, Typed},
    verify_err,
};

use super::{
    attr_interfaces::TypedAttrInterface,
    attributes::TypeAttr,
    op_interfaces::{
        self, IsolatedFromAboveInterface, OneRegionInterface, OneResultInterface,
        SingleBlockRegionInterface, SymbolOpInterface, SymbolTableInterface, ZeroOpdInterface,
    },
    types::{FunctionType, UnitType},
};

/// Represents a module, a top level container operation.
///
/// See MLIR's [builtin.module](https://mlir.llvm.org/docs/Dialects/Builtin/#builtinmodule-mlirmoduleop).
/// It contains a single [SSACFG](super::op_interfaces::RegionKind::SSACFG)
/// region containing a single block which can contain any operations and
/// does not have a terminator.
#[def_op("builtin.module")]
#[derive_op_interface_impl(
    OneRegionInterface,
    SingleBlockRegionInterface,
    SymbolTableInterface,
    SymbolOpInterface,
    IsolatedFromAboveInterface,
    ZeroOpdInterface,
    ZeroResultInterface,
    NoTerminatorInterface
)]
pub struct ModuleOp;

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
            Self::get_concrete_op_info(),
            vec![],
            vec![],
            vec![],
            0,
        );
        let mut parser =
            spaced(token('@').with(Identifier::parser(()))).and(spaced(Region::parser(op)));
        parser
            .parse_stream(state_stream)
            .map(|(name, _region)| -> OpObj {
                let op = ModuleOp { op };
                op.set_symbol_name(state_stream.state.ctx, name);
                OpObj::new(op)
            })
            .into()
    }
}

impl_verify_succ!(ModuleOp);

impl ModuleOp {
    /// Create a new [ModuleOp].
    /// The underlying [Operation] is not linked to a [BasicBlock].
    /// The returned module has a single [crate::region::Region] with a single (BasicBlock)[crate::basic_block::BasicBlock].
    pub fn new(ctx: &mut Context, name: Identifier) -> ModuleOp {
        let op = Operation::new(ctx, Self::get_concrete_op_info(), vec![], vec![], vec![], 1);
        let opop = ModuleOp { op };
        opop.set_symbol_name(ctx, name);

        // Create an empty block.
        let region = opop.get_region(ctx);
        let block = BasicBlock::new(ctx, None, vec![]);
        block.insert_at_front(region, ctx);

        opop
    }
}

/// An operation with a name containing a single SSA control-flow-graph region.
/// See MLIR's [func.func](https://mlir.llvm.org/docs/Dialects/Func/#funcfunc-mlirfuncfuncop).
#[def_op("builtin.func")]
#[derive_op_interface_impl(
    OneRegionInterface,
    SymbolOpInterface,
    IsolatedFromAboveInterface,
    ZeroOpdInterface,
    ZeroResultInterface
)]
#[derive_attr_get_set(func_type : TypeAttr)]
pub struct FuncOp;

impl FuncOp {
    /// Create a new [FuncOp].
    /// The returned function has a single region with an empty `entry` block.
    pub fn new(ctx: &mut Context, name: Identifier, ty: TypePtr<FunctionType>) -> Self {
        let ty_attr = TypeAttr::new(ty.into());
        let op = Operation::new(ctx, Self::get_concrete_op_info(), vec![], vec![], vec![], 1);

        // Create an empty entry block.
        let arg_types = ty.deref(ctx).arg_types().clone();
        let region = op.deref_mut(ctx).get_region(0);
        let body = BasicBlock::new(ctx, Some("entry".try_into().unwrap()), arg_types);
        body.insert_at_front(region, ctx);

        let opop = FuncOp { op };
        opop.set_symbol_name(ctx, name);
        opop.set_attr_func_type(ctx, ty_attr);

        opop
    }

    /// Get the function signature (type).
    pub fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        attr_cast::<dyn TypedAttrInterface>(&*self.get_attr_func_type(ctx).unwrap())
            .unwrap()
            .get_type(ctx)
    }

    /// Get the entry block of this function.
    pub fn get_entry_block(&self, ctx: &Context) -> Ptr<BasicBlock> {
        self.get_region(ctx).deref(ctx).get_head().unwrap()
    }
}

impl Typed for FuncOp {
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.get_type(ctx)
    }
}

impl Printable for FuncOp {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        typed_symb_op_header(self).fmt(ctx, state, f)?;
        write!(f, " ")?;
        let mut attributes_to_print_separately =
            self.op.deref(ctx).attributes.clone_skip_outlined();
        attributes_to_print_separately
            .0
            .retain(|key, _| key != &*ATTR_KEY_FUNC_TYPE && key != &*ATTR_KEY_SYM_NAME);
        if !attributes_to_print_separately.0.is_empty() {
            indented_block!(state, {
                write!(f, "{}", indented_nl(state))?;
                attributes_to_print_separately.fmt(ctx, state, f)?;
            });
        }
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
            Self::get_concrete_op_info(),
            vec![],
            vec![],
            vec![],
            0,
        );

        let mut parser = (
            spaced(token('@').with(Identifier::parser(()))).skip(spaced(token(':'))),
            spaced(type_parser()),
            spaced(optional(AttributeDict::parser(()))),
            spaced(Region::parser(op)),
        );

        // Parse and build the function, providing name and type details.
        parser
            .parse_stream(state_stream)
            .map(|(fname, fty, attributes, _region)| -> OpObj {
                let ctx = &mut state_stream.state.ctx;
                op.deref_mut(ctx).attributes = attributes.unwrap_or_default();
                let ty_attr = TypeAttr::new(fty);
                let opop = FuncOp { op };
                opop.set_symbol_name(ctx, fname);
                opop.set_attr_func_type(ctx, ty_attr);
                OpObj::new(opop)
            })
            .into()
    }
}

#[derive(Error, Debug)]
#[error("function does not have function type")]
pub struct FuncOpTypeErr;

impl Verify for FuncOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let op = &*self.get_operation().deref(ctx);
        let ty = self.get_type(ctx);
        if !(ty.deref(ctx).is::<FunctionType>()) {
            return verify_err!(op.loc(), FuncOpTypeErr);
        }
        Ok(())
    }
}

/// A placeholder during parsing to refer to yet undefined operations.
/// MLIR [uses](https://github.com/llvm/llvm-project/blob/185b81e034ba60081023b6e59504dfffb560f3e3/mlir/lib/AsmParser/Parser.cpp#L1075)
/// [UnrealizedConversionCastOp](https://mlir.llvm.org/docs/Dialects/Builtin/#builtinunrealized_conversion_cast-unrealizedconversioncastop)
/// for this purpose.
#[def_op("builtin.forward_ref")]
#[derive_op_interface_impl(OneResultInterface, ZeroOpdInterface)]
pub struct ForwardRefOp;

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

#[derive(Error, Debug)]
#[error("{0} is a temporary Op during parsing. It must not exit in a well-formed program.")]
pub struct ForwardRefOpExistenceErr(String);

impl Verify for ForwardRefOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        verify_err!(
            self.loc(ctx),
            ForwardRefOpExistenceErr(self.get_result(ctx).unique_name(ctx).into())
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
    pub fn new(ctx: &mut Context) -> Self {
        let ty = UnitType::get(ctx).into();
        let op = Operation::new(
            ctx,
            Self::get_concrete_op_info(),
            vec![ty],
            vec![],
            vec![],
            0,
        );
        ForwardRefOp { op }
    }
}
