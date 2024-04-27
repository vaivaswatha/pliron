//! An [Op] is a thin wrapper arround an [Operation], providing
//! API specific to the [OpId] of that Operation.
//!
//! See MLIR's [Op](https://mlir.llvm.org/docs/Tutorials/Toy/Ch-2/#op-vs-operation-using-mlir-operations).
//!
//! New [Op]s can be easily declared using the [def_op](pliron_derive::def_op)
//! proc macro from the pliron-derive crate.
//!
//! Common semantics, API and behaviour of [Op]s are
//! abstracted into Op interfaces. Interfaces in pliron capture MLIR
//! functionality of both [Traits](https://mlir.llvm.org/docs/Traits/)
//! and [Interfaces](https://mlir.llvm.org/docs/Interfaces/).
//! Interfaces must all implement an associated function named `verify` with
//! the type [OpInterfaceVerifier].
//!
//! [Op]s that implement an interface must do so using the
//! [impl_op_interface](crate::impl_op_interface) macro.
//! This ensures that the interface verifier is automatically called,
//! and that a `&dyn Op` object can be [cast](op_cast) into an interface object,
//! (or that it can be checked if the interface is [implemented](op_impls))
//! with ease.
//!
//! [OpObj]s can be downcasted to their concrete types using
//! [downcast_rs](https://docs.rs/downcast-rs/1.2.0/downcast_rs/index.html#example-without-generics).

use combine::{
    parser::{self},
    token, Parser,
};
use downcast_rs::{impl_downcast, Downcast};
use std::{
    fmt::{self, Display},
    ops::Deref,
};
use thiserror::Error;

use crate::{
    common_traits::Verify,
    context::{Context, Ptr},
    dialect::{Dialect, DialectName},
    dialects::builtin::types::FunctionType,
    error::Result,
    identifier::Identifier,
    input_err,
    irfmt::{
        parsers::{
            delimited_list_parser, location, process_parsed_ssa_defs, spaced, ssa_opd_parser,
        },
        printers::{functional_type, iter_with_sep},
    },
    location::Location,
    operation::Operation,
    parsable::{IntoParseResult, Parsable, ParseResult, ParserFn, StateStream},
    printable::{self, Printable},
    r#type::Typed,
};

#[derive(Clone, Hash, PartialEq, Eq)]
/// An Op's name (not including it's dialect).
pub struct OpName(String);

impl OpName {
    /// Create a new OpName.
    pub fn new(name: &str) -> OpName {
        OpName(name.to_string())
    }
}

impl Deref for OpName {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Printable for OpName {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl Parsable for OpName {
    type Arg = ();
    type Parsed = OpName;

    fn parse<'a>(
        state_stream: &mut crate::parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        Identifier::parser(())
            .map(|name| OpName::new(&name))
            .parse_stream(state_stream)
            .into()
    }
}

impl Display for OpName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A combination of an [Op]'s name and its dialect.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct OpId {
    pub dialect: DialectName,
    pub name: OpName,
}

impl Printable for OpId {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl Parsable for OpId {
    type Arg = ();
    type Parsed = OpId;

    // Parses (but does not validate) a OpId.
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        let mut parser = DialectName::parser(())
            .skip(parser::char::char('.'))
            .and(OpName::parser(()))
            .map(|(dialect, name)| OpId { dialect, name });
        parser.parse_stream(state_stream).into()
    }
}

impl Display for OpId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.dialect, self.name)
    }
}

pub(crate) type OpCreator = fn(Ptr<Operation>) -> OpObj;

/// A wrapper around [Operation] for Op(code) specific work.
/// All per-instance data must be in the underyling Operation,
/// which means that [OpObj]s are light-weight.
///
/// See [module](crate::op) documentation for more information.
pub trait Op: Downcast + Verify + Printable {
    /// Get the underlying IR Operation
    fn get_operation(&self) -> Ptr<Operation>;
    /// Create a new Op object, by wrapping around an operation.
    fn wrap_operation(op: Ptr<Operation>) -> OpObj
    where
        Self: Sized;
    /// Get this Op's OpId
    fn get_opid(&self) -> OpId;
    /// Get this Op's OpId, without self reference.
    fn get_opid_static() -> OpId
    where
        Self: Sized;

    /// Verify all interfaces implemented by this op.
    fn verify_interfaces(&self, ctx: &Context) -> Result<()>;

    /// Register Op in Context and add it to dialect.
    fn register(
        ctx: &mut Context,
        dialect: &mut Dialect,
        op_parser: ParserFn<Vec<(Identifier, Location)>, OpObj>,
    ) where
        Self: Sized,
    {
        match ctx.ops.entry(Self::get_opid_static()) {
            std::collections::hash_map::Entry::Occupied(_) => (),
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert(Self::wrap_operation);
                dialect.add_op(Self::get_opid_static(), op_parser);
            }
        }
    }
}
impl_downcast!(Op);

/// Create [OpObj] from [`Ptr<Operation>`](Operation)
pub(crate) fn from_operation(ctx: &Context, op: Ptr<Operation>) -> OpObj {
    let opid = op.deref(ctx).get_opid();
    (ctx.ops
        .get(&opid)
        .unwrap_or_else(|| panic!("Unregistered Op {}", opid.disp(ctx))))(op)
}

/// [Op] objects are boxed and stored in the IR.
pub type OpObj = Box<dyn Op>;

/// Cast reference to an [Op] object to an interface reference.
pub fn op_cast<T: ?Sized + Op>(op: &dyn Op) -> Option<&T> {
    crate::trait_cast::any_to_trait::<T>(op.as_any())
}

/// Does this [Op] object implement interface T?
pub fn op_impls<T: ?Sized + Op>(op: &dyn Op) -> bool {
    op_cast::<T>(op).is_some()
}

/// Every op interface must have a function named `verify` with this type.
pub type OpInterfaceVerifier = fn(&dyn Op, &Context) -> Result<()>;

/// Implement an Op Interface for an Op. The interface trait must define
/// a `verify` function with type [OpInterfaceVerifier]
///
/// Usage:
/// ```
/// #[def_op("dialect.name")]
/// struct MyOp {};
///
/// trait MyOpInterface: Op {
///     fn gubbi(&self);
///     fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
///         where
///         Self: Sized,
///     {
///         Ok(())
///     }
/// }
/// impl_op_interface!(
///     MyOpInterface for MyOp
///     {
///         fn gubbi(&self) { println!("gubbi"); }
///     }
/// );
/// # use pliron_derive::def_op;
/// # use pliron::{
/// #     op::Op, impl_op_interface,
/// #     context::Context, error::Result,
/// #     common_traits::Verify
/// # };
/// # pliron::impl_verify_succ!(MyOp);
/// # pliron::impl_canonical_syntax!(MyOp);
#[macro_export]
macro_rules! impl_op_interface {
    ($intr_name:ident for $op_name:ident { $($tt:tt)* }) => {
        inventory::submit! {
            $op_name::build_interface_verifier(<$op_name as $intr_name>::verify)
        }

        $crate::type_to_trait!($op_name, $intr_name);
        impl $intr_name for $op_name {
            $($tt)*
        }
    };
}

/// Printer for an [Op] in canonical syntax.
/// `res_1: type_1, res_2: type_2, ... res_n: type_n = op_id (opd_1, opd_2, ... opd_n) : function-type`
/// TODO: Handle operations with regions, attributes.
pub fn canonical_syntax_fmt(
    op: OpObj,
    ctx: &Context,
    _state: &printable::State,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    let sep = printable::ListSeparator::CharSpace(',');
    let op = op.get_operation().deref(ctx);
    let operands = iter_with_sep(op.operands(), sep);
    let op_type = functional_type(
        iter_with_sep(op.results().map(|res| res.get_type(ctx)), sep),
        iter_with_sep(op.operands().map(|opd| opd.get_type(ctx)), sep),
    );

    if op.get_num_results() != 0 {
        let results = iter_with_sep(op.results(), sep);
        write!(f, "{} = ", results.disp(ctx))?;
    }
    let ret = write!(
        f,
        "{} ({}) : {}",
        op.get_opid().disp(ctx),
        operands.disp(ctx),
        op_type.disp(ctx),
    );
    ret
}

#[derive(Error, Debug)]
pub enum CanonicalSyntaxParseError {
    #[error("Type specifies {num_res_ty} results, but operation has {num_res} results")]
    ResultsMismatch { num_res_ty: usize, num_res: usize },
    #[error("Type specifies {num_opd_ty} operands, but operation has {num_opd} operands")]
    OperandsMismatch { num_opd_ty: usize, num_opd: usize },
}

/// Parse an [Op] in canonical syntax.
/// See [canonical_syntax_fmt] for the syntax.
pub fn canonical_syntax_parse<'a>(
    opid: OpId,
    state_stream: &mut StateStream<'a>,
    results: Vec<(Identifier, Location)>,
) -> ParseResult<'a, OpObj> {
    // Results and opid have already been parsed. Continue after that.
    delimited_list_parser('(', ')', ',', ssa_opd_parser())
        .skip(spaced(token(':')))
        .and((location(), FunctionType::parser(())))
        .then(move |(operands, (fty_loc, fty))| {
            let opid = opid.clone();
            let results = results.clone();
            let fty_loc = fty_loc.clone();
            combine::parser(move |parsable_state: &mut StateStream<'a>| {
                let results = results.clone();
                let ctx = &mut parsable_state.state.ctx;
                let results_types = fty.deref(ctx).get_results().to_vec();
                let operands_types = fty.deref(ctx).get_inputs().to_vec();
                if results_types.len() != results.len() {
                    input_err!(
                        fty_loc.clone(),
                        CanonicalSyntaxParseError::ResultsMismatch {
                            num_res_ty: results_types.len(),
                            num_res: results.len()
                        }
                    )?
                }
                if operands.len() != operands_types.len() {
                    input_err!(
                        fty_loc.clone(),
                        CanonicalSyntaxParseError::OperandsMismatch {
                            num_opd_ty: operands_types.len(),
                            num_opd: operands.len()
                        }
                    )?
                }
                let opr = Operation::new(ctx, opid.clone(), results_types, operands.clone(), 0);
                let op = from_operation(ctx, opr);
                process_parsed_ssa_defs(parsable_state, &results, opr)?;
                Ok(op).into_parse_result()
            })
        })
        .parse_stream(state_stream)
        .into()
}

/// Parser for an [Op] in canonical syntax.
/// See [canonical_syntax_fmt] for the syntax.
pub fn canonical_syntax_parser<'a>(
    opid: OpId,
    results: Vec<(Identifier, Location)>,
) -> Box<dyn Parser<StateStream<'a>, Output = OpObj, PartialState = ()> + 'a> {
    combine::parser(move |parsable_state: &mut StateStream<'a>| {
        canonical_syntax_parse(opid.clone(), parsable_state, results.clone())
    })
    .boxed()
}

/// Shorthand for defining a canonical syntax [Printable] and [Parsable] for an [Op]
/// ```
/// use pliron_derive::def_op;
/// use pliron::{impl_canonical_syntax, impl_verify_succ};
/// #[def_op("dialect.name")]
/// pub struct MyOp {};
/// impl_canonical_syntax!(MyOp);
/// impl_verify_succ!(MyOp);
/// ```
#[macro_export]
macro_rules! impl_canonical_syntax {
    ($op_name:path) => {
        // Implement [Printable]($crate::printable::Printable)
        impl $crate::printable::Printable for $op_name {
            fn fmt(
                &self,
                ctx: &$crate::context::Context,
                state: &$crate::printable::State,
                f: &mut std::fmt::Formatter<'_>,
            ) -> std::fmt::Result {
                $crate::op::canonical_syntax_fmt(Box::new(*self), ctx, state, f)
            }
        }

        // Implement [Parsable]($crate::parsable::Parsable)
        impl $crate::parsable::Parsable for $op_name {
            type Arg = Vec<($crate::identifier::Identifier, $crate::location::Location)>;
            type Parsed = $crate::op::OpObj;
            fn parse<'a>(
                state_stream: &mut $crate::parsable::StateStream<'a>,
                results: Self::Arg,
            ) -> $crate::parsable::ParseResult<'a, Self::Parsed> {
                $crate::op::canonical_syntax_parser(
                    <Self as $crate::op::Op>::get_opid_static(),
                    results,
                )
                .parse_stream(state_stream)
                .into()
            }
        }
    };
}
