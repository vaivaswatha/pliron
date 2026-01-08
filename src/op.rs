//! An [Op] is a thin wrapper arround an [Operation], providing
//! API specific to the [OpId] of that Operation.
//!
//! See MLIR's [Op](https://mlir.llvm.org/docs/Tutorials/Toy/Ch-2/#op-vs-operation-using-mlir-operations).
//!
//! New [Op]s can be easily declared using the [def_op](pliron::derive::def_op)
//! proc macro from the pliron-derive crate.
//!
//! Common semantics, API and behaviour of [Op]s are
//! abstracted into Op interfaces. Interfaces in pliron capture MLIR
//! functionality of both [Traits](https://mlir.llvm.org/docs/Traits/)
//! and [Interfaces](https://mlir.llvm.org/docs/Interfaces/).
//! Interfaces must all implement an associated function named `verify` with
//! the type [OpInterfaceVerifier].
//!
//! Interfaces are rust Trait definitions annotated with the attribute macro
//! [op_interface](pliron::derive::op_interface). The attribute ensures that any
//! verifiers of super-interfaces (specified as super traits) are run prior to
//! the verifier of this interface.
//!
//! [Op]s that implement an interface must annotate the implementation with
//! [op_interface_impl](pliron::derive::op_interface_impl) macro to ensure that
//! the interface verifier is automatically called during verification
//! and that a `&dyn Op` object can be [cast](op_cast) into an interface object,
//! (or that it can be checked if the interface is [implemented](op_impls))
//! with ease.
//!
//! Use [verify_op] to verify an [Op] object. It calls the internal
//! [Operation]'s `verify` method, which in turn calls the verifiers for operands,
//! results, attributes and regions, and then the verifiers for all interfaces.
//!
//! [OpObj]s can be downcasted to their concrete types using
//! [downcast_rs](https://docs.rs/downcast-rs/1.2.0/downcast_rs/index.html#example-without-generics).

use combine::{
    Parser,
    parser::{self, char::spaces},
    token,
};
use downcast_rs::{Downcast, impl_downcast};
use dyn_clone::DynClone;
use rustc_hash::FxHashMap;
use std::{
    fmt::{self, Display},
    hash::Hash,
    ops::Deref,
    sync::LazyLock,
};
use thiserror::Error;

use crate::{
    attribute::AttributeDict,
    builtin::{type_interfaces::FunctionTypeInterface, types::FunctionType},
    common_traits::{Named, Verify},
    context::{Context, Ptr},
    dialect::DialectName,
    identifier::Identifier,
    impl_printable_for_display, input_err,
    irfmt::{
        parsers::{
            block_opd_parser, delimited_list_parser, location, process_parsed_ssa_defs, spaced,
            ssa_opd_parser, zero_or_more_parser,
        },
        printers::{functional_type, iter_with_sep},
    },
    location::{Located, Location},
    operation::Operation,
    parsable::{IntoParseResult, Parsable, ParseResult, ParserFn, StateStream},
    printable::{self, Printable},
    region::Region,
    result::Result,
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

impl_printable_for_display!(OpName);

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

impl_printable_for_display!(OpId);

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

pub(crate) type ConcreteOpInfo = (fn(Ptr<Operation>) -> OpObj, std::any::TypeId);

/// A wrapper around [Operation] for Op(code) specific work.
/// All per-instance data must be in the underyling Operation,
/// which means that [OpObj]s are light-weight.
///
/// See [module](crate::op) documentation for more information.
pub trait Op: Downcast + Verify + Printable + DynClone {
    /// Get the underlying IR Operation
    fn get_operation(&self) -> Ptr<Operation>;

    /// Create a new [OpObj], by boxing [Op].
    ///
    /// **WARNING**: Does not check that the operation is of the correct OpId.
    fn wrap_operation(op: Ptr<Operation>) -> OpObj
    where
        Self: Sized;

    /// Create a concrete [Op] from an [Operation].
    ///
    /// **WARNING**: Does not check that the operation is of the correct OpId.
    fn from_operation(op: Ptr<Operation>) -> Self
    where
        Self: Sized;

    /// Get details about the concrete Op type.
    fn get_concrete_op_info() -> ConcreteOpInfo
    where
        Self: Sized,
    {
        (Self::wrap_operation, std::any::TypeId::of::<Self>())
    }
    /// Get this Op's OpId
    fn get_opid(&self) -> OpId;

    /// Get this Op's OpId, without self reference.
    fn get_opid_static() -> OpId
    where
        Self: Sized;

    /// Verify all interfaces implemented by this op.
    fn verify_interfaces(&self, ctx: &Context) -> Result<()>;

    /// Register Op in Context and add it to its dialect.
    fn register(ctx: &mut Context, op_parser: ParserFn<Vec<(Identifier, Location)>, OpObj>)
    where
        Self: Sized,
    {
        let opid = Self::get_opid_static();
        let dialect = opid.dialect.clone();
        let dialect = ctx
            .dialects
            .get_mut(&dialect)
            .unwrap_or_else(|| panic!("Unregistered dialect {dialect}"));
        dialect.add_op(Self::get_opid_static(), op_parser);
    }

    /// Get Op's location
    fn loc(&self, ctx: &Context) -> Location {
        self.get_operation().deref(ctx).loc()
    }
}
impl_downcast!(Op);
dyn_clone::clone_trait_object!(Op);

/// [Op] objects are boxed and stored in the IR.
pub type OpObj = OpBox;

impl PartialEq for OpObj {
    fn eq(&self, other: &Self) -> bool {
        self.as_ref()
            .get_operation()
            .eq(&other.as_ref().get_operation())
    }
}

/// Verify an [Op] object. It just calls the `verify` method of the operation.
pub fn verify_op(op: &dyn Op, ctx: &Context) -> Result<()> {
    op.get_operation().verify(ctx)
}

impl Eq for OpObj {}

impl Hash for OpObj {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_ref().get_operation().hash(state)
    }
}

/// Cast reference to an [Op] object to an interface reference.
pub fn op_cast<T: ?Sized + Op>(op: &dyn Op) -> Option<&T> {
    crate::utils::trait_cast::any_to_trait::<T>(op.as_any())
}

/// Does this [Op] object implement interface T?
pub fn op_impls<T: ?Sized + Op>(op: &dyn Op) -> bool {
    op_cast::<T>(op).is_some()
}

/// Every op interface must have a function named `verify` with this type.
pub type OpInterfaceVerifier = fn(&dyn Op, &Context) -> Result<()>;

/// Type alias for op interface verifier information
/// [Op]s paired with every interface it implements (and the verifier for that interface).
type OpInterfaceVerifierInfo = (OpId, (std::any::TypeId, OpInterfaceVerifier));

/// Type alias for op interface dependency information
/// All interfaces mapped to their super-interfaces
type OpInterfaceDepsInfo = (std::any::TypeId, Vec<std::any::TypeId>);

#[doc(hidden)]
#[cfg(not(target_family = "wasm"))]
pub mod statics {
    use super::*;

    #[linkme::distributed_slice]
    pub static OP_INTERFACE_VERIFIERS: [LazyLock<OpInterfaceVerifierInfo>] = [..];

    #[linkme::distributed_slice]
    pub static OP_INTERFACE_DEPS: [LazyLock<OpInterfaceDepsInfo>] = [..];

    pub fn get_op_interface_verifiers()
    -> impl Iterator<Item = &'static LazyLock<OpInterfaceVerifierInfo>> {
        OP_INTERFACE_VERIFIERS.iter()
    }

    pub fn get_op_interface_deps() -> impl Iterator<Item = &'static LazyLock<OpInterfaceDepsInfo>> {
        OP_INTERFACE_DEPS.iter()
    }
}

#[cfg(target_family = "wasm")]
pub mod statics {
    use super::*;
    use crate::utils::inventory::LazyLockWrapper;

    inventory::collect!(LazyLockWrapper<OpInterfaceVerifierInfo>);

    inventory::collect!(LazyLockWrapper<OpInterfaceDepsInfo, OpId>);

    pub fn get_op_interface_verifiers()
    -> impl Iterator<Item = &'static LazyLock<OpInterfaceVerifierInfo>> {
        inventory::iter::<LazyLockWrapper<OpInterfaceVerifierInfo>>().map(|llw| llw.0)
    }

    pub fn get_op_interface_deps() -> impl Iterator<Item = &'static LazyLock<OpInterfaceDepsInfo>> {
        inventory::iter::<LazyLockWrapper<OpInterfaceDepsInfo, OpId>>().map(|llw| llw.0)
    }
}

pub use statics::*;

#[doc(hidden)]
/// A map from every [Op] to its ordered (as per interface deps) list of interface verifiers.
/// An interface's super-interfaces are to be verified before it itself is.
pub static OP_INTERFACE_VERIFIERS_MAP: LazyLock<
    FxHashMap<OpId, Vec<(std::any::TypeId, OpInterfaceVerifier)>>,
> = LazyLock::new(|| {
    use std::any::TypeId;
    // Collect OP_INTERFACE_VERIFIERS into an [OpId] indexed map.
    let mut op_intr_verifiers = FxHashMap::default();
    for lazy in get_op_interface_verifiers() {
        let (op_id, (type_id, verifier)) = (**lazy).clone();
        op_intr_verifiers
            .entry(op_id)
            .and_modify(|verifiers: &mut Vec<(TypeId, OpInterfaceVerifier)>| {
                verifiers.push((type_id, verifier))
            })
            .or_insert(vec![(type_id, verifier)]);
    }

    // Collect interface deps into a map.
    let interface_deps: FxHashMap<_, _> = get_op_interface_deps()
        .map(|lazy| (**lazy).clone())
        .collect();

    // Assign an integer to each interface, such that if y depends on x
    // i.e., x is a super-interface of y, then dep_sort_idx[x] < dep_sort_idx[y]
    let mut dep_sort_idx = FxHashMap::<TypeId, u32>::default();
    let mut sort_idx = 0;
    fn assign_idx_to_intr(
        interface_deps: &FxHashMap<TypeId, Vec<TypeId>>,
        dep_sort_idx: &mut FxHashMap<TypeId, u32>,
        sort_idx: &mut u32,
        intr: &TypeId,
    ) {
        if dep_sort_idx.contains_key(intr) {
            return;
        }

        // Assign index to every dependent first. We don't bother to check for cyclic
        // dependences since super interfaces are also super traits in Rust.
        let deps = interface_deps
            .get(intr)
            .expect("Expect every interface to have a (possibly empty) list of dependences");
        for dep in deps {
            assign_idx_to_intr(interface_deps, dep_sort_idx, sort_idx, dep);
        }

        // Assign an index to the current interface.
        dep_sort_idx.insert(*intr, *sort_idx);
        *sort_idx += 1;
    }

    // Assign dep_sort_idx to every interface.
    for lazy in get_op_interface_deps() {
        let (intr, _deps) = &**lazy;
        assign_idx_to_intr(&interface_deps, &mut dep_sort_idx, &mut sort_idx, intr);
    }

    for verifiers in op_intr_verifiers.values_mut() {
        // sort verifiers based on its dep_sort_idx.
        verifiers.sort_by(|(a, _), (b, _)| dep_sort_idx[a].cmp(&dep_sort_idx[b]));
    }

    op_intr_verifiers
});

/// Printer for an [Op] in canonical syntax.
/// `res_1, res_2, ... res_n =
///      op_id (opd_1, opd_2, ... opd_n) [succ_1, succ_2, ... succ_n] [attr-dict]: function-type (regions)*`
pub fn canonical_syntax_print(
    op: OpObj,
    ctx: &Context,
    state: &printable::State,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    let sep = printable::ListSeparator::CharSpace(',');
    let opid = op.as_ref().get_opid();
    let op = op.as_ref().get_operation().deref(ctx);
    let operands = iter_with_sep(op.operands(), sep);
    let successors = iter_with_sep(
        op.successors()
            .map(|succ| "^".to_string() + &succ.unique_name(ctx)),
        sep,
    );
    let op_type = functional_type(
        iter_with_sep(op.operands().map(|opd| opd.get_type(ctx)), sep),
        iter_with_sep(op.results().map(|res| res.get_type(ctx)), sep),
    );
    let regions = iter_with_sep(op.regions(), printable::ListSeparator::Newline);

    if op.get_num_results() != 0 {
        let results = iter_with_sep(op.results(), sep);
        write!(f, "{} = ", results.disp(ctx))?;
    }

    write!(
        f,
        "{} ({}) [{}] {}: {}",
        opid.disp(ctx),
        operands.disp(ctx),
        successors.disp(ctx),
        op.attributes.clone_skip_outlined().disp(ctx),
        op_type.disp(ctx),
    )?;

    if op.num_regions() > 0 {
        regions.fmt(ctx, state, f)?;
    }
    Ok(())
}

#[derive(Error, Debug)]
pub enum CanonicalSyntaxParseError {
    #[error("Type specifies {num_res_ty} results, but operation has {num_res} results")]
    ResultsMismatch { num_res_ty: usize, num_res: usize },
    #[error("Type specifies {num_opd_ty} operands, but operation has {num_opd} operands")]
    OperandsMismatch { num_opd_ty: usize, num_opd: usize },
}

/// Parse an [Op] in canonical syntax.
/// See [canonical_syntax_print] for the syntax.
pub fn canonical_syntax_parse<'a, T: Op>(
    state_stream: &mut StateStream<'a>,
    results: Vec<(Identifier, Location)>,
) -> ParseResult<'a, OpObj> {
    // Results and opid have already been parsed. Continue after that.
    let mut without_regions = delimited_list_parser('(', ')', ',', ssa_opd_parser())
        .and(spaces().with(delimited_list_parser('[', ']', ',', block_opd_parser())))
        .and(spaces().with(AttributeDict::parser(())))
        .skip(spaced(token(':')))
        .and((location(), FunctionType::parser(())))
        .then(
            move |(((operands, successors), attr_dict), (fty_loc, fty))| {
                let results = results.clone();
                let fty_loc = fty_loc.clone();
                combine::parser(move |parsable_state: &mut StateStream<'a>| {
                    let results = results.clone();
                    let ctx = &mut parsable_state.state.ctx;
                    let results_types = fty.deref(ctx).res_types().to_vec();
                    let operands_types = fty.deref(ctx).arg_types().to_vec();
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
                    let opr = Operation::new(
                        ctx,
                        T::get_concrete_op_info(),
                        results_types,
                        operands.clone(),
                        successors.clone(),
                        0,
                    );
                    opr.deref_mut(ctx).attributes = attr_dict.clone();
                    process_parsed_ssa_defs(parsable_state, &results, opr)?;
                    Ok(opr).into_parse_result()
                })
            },
        );

    let op = without_regions.parse_stream(state_stream).into_result()?.0;
    zero_or_more_parser(Region::parser(op))
        .parse_stream(state_stream)
        .into_result()?;
    let op = T::wrap_operation(op);
    Ok(op).into_parse_result()
}

/// Parser for an [Op] in canonical syntax.
/// See [canonical_syntax_print] for the syntax.
pub fn canonical_syntax_parser<'a, T: Op>(
    results: Vec<(Identifier, Location)>,
) -> Box<dyn Parser<StateStream<'a>, Output = OpObj, PartialState = ()> + 'a> {
    combine::parser(move |parsable_state: &mut StateStream<'a>| {
        canonical_syntax_parse::<T>(parsable_state, results.clone())
    })
    .boxed()
}

/// This must always be the same as any concrete [Op] object.
#[derive(Clone)]
struct OpData {
    #[allow(unused)]
    op: Ptr<Operation>,
}

/// A stack allocated alternative to [Box] for [Op] objects.
#[derive(Clone)]
pub struct OpBox {
    data: OpData,
    vtable_ptr: *const (),
}

impl OpBox {
    /// Create a new [OpBox] from a concrete [Op] object.
    pub fn new<T: Op>(op: T) -> Self {
        /// Static assertion to ensure that concrete [Op]s
        /// always are the same as our [OpData] struct.
        struct StaticAsserter<S>(S);
        impl<S> StaticAsserter<S> {
            const ASSERTTION: () = {
                // Ensure that OpData and T have the same size.
                assert!(
                    std::mem::size_of::<OpData>() == std::mem::size_of::<S>(),
                    "OpBox can only box Op objects"
                );
            };
        }
        let _: () = StaticAsserter::<T>::ASSERTTION;

        let dyn_ref: &dyn Op = &op;
        let (_, vtable_ptr) =
            unsafe { std::mem::transmute::<&dyn Op, (*const T, *const ())>(dyn_ref) };

        OpBox {
            data: OpData {
                op: op.get_operation(),
            },
            vtable_ptr,
        }
    }

    /// Get a reference to the underlying [Op] object.
    pub fn op_ref(&self) -> &dyn Op {
        unsafe {
            let dyn_ref: &dyn Op =
                std::mem::transmute::<(&OpData, *const ()), &dyn Op>((&self.data, self.vtable_ptr));
            dyn_ref
        }
    }

    /// Downcast this [OpBox] to a concrete [Op] type.
    pub fn downcast<T: Op>(self) -> Option<T> {
        self.as_ref()
            .downcast_ref::<T>()
            .map(|op| T::from_operation(op.get_operation()))
    }
}

impl AsRef<dyn Op> for OpBox {
    fn as_ref(&self) -> &dyn Op {
        self.op_ref()
    }
}

impl Deref for OpBox {
    type Target = dyn Op;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

#[cfg(test)]
mod tests {

    use pliron::result::Result;
    use rustc_hash::{FxHashMap, FxHashSet};
    use std::any::TypeId;

    use crate::verify_err_noloc;

    use super::{OP_INTERFACE_VERIFIERS_MAP, get_op_interface_deps};

    #[test]
    /// For every interface that an [Op] implements, ensure that the interface verifiers
    /// get called in the right order, with super-interface verifiers called before their
    /// sub-interface verifier.
    fn check_verifiers_deps() -> Result<()> {
        // Collect interface deps into a map.
        let interface_deps: FxHashMap<_, _> = get_op_interface_deps()
            .map(|lazy| (**lazy).clone())
            .collect();

        for (op, intrs) in OP_INTERFACE_VERIFIERS_MAP.iter() {
            let mut satisfied_deps = FxHashSet::<TypeId>::default();
            for (intr, _) in intrs {
                let deps = interface_deps.get(intr).ok_or_else(|| {
                    let err: Result<()> = verify_err_noloc!(
                       "Missing deps list for TypeId {:?} when checking verifier dependences for {}",
                        intr,
                        op
                    );
                    err.unwrap_err()
                })?;
                for dep in deps {
                    if !satisfied_deps.contains(dep) {
                        return verify_err_noloc!(
                            "For {}, depencence {:?} not satisfied for {:?}",
                            op,
                            dep,
                            intr
                        );
                    }
                }
                satisfied_deps.insert(*intr);
            }
        }

        Ok(())
    }
}
