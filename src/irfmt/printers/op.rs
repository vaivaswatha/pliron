//! Object specific printers and ir_format directives.

use std::fmt;

use crate::{
    basic_block::BasicBlock,
    common_traits::Named,
    context::{private::ArenaObj, Context, Ptr},
    dialects::builtin::op_interfaces::{OneRegionInterface, SymbolOpInterface},
    op::Op,
    operation::{Operand, Operation},
    printable::{ListSeparator, Printable, State},
    r#type::{Type, Typed},
    use_def_lists::{DefUseParticipant, Value},
};

use super::{concat, enclosed, iter_with_sep, list_with_sep, literal, quoted, PrinterFn};

#[macro_export]
macro_rules! op_operation_generic_format_directive {
    ($ctx:ident, $self:ident) => {
        $crate::irfmt::printers::op::operation_generic_format(*$self)
    };
}
pub use op_operation_generic_format_directive;

#[macro_export]
macro_rules! op_results_directive {
    ($ctx:ident, $op:ident) => {{
        use $crate::op::Op;
        $op.get_operation().deref($ctx).results()
    }};
}
pub use op_results_directive;

#[macro_export]
macro_rules! op_check_directive {
    ($ctx:ident, $self:ident, $ty:expr) => {
        $crate::irfmt::printers::check($ctx, $ty)
    };
}
pub use op_check_directive;

#[macro_export]
macro_rules! op_operands_directive {
    ($ctx:ident, $op:ident) => {{
        let operation = $op.get_operation().deref($ctx);
        $crate::irfmt::printers::op::OperandsList::new("(", ")", &operation.operands)
    }};
}
pub use op_operands_directive;

/// Print the operations of an Operation.
pub fn operands(op: &Operation) -> OperandsList<'_, Value> {
    OperandsList::new("(", ")", op.operands.as_slice())
}

#[macro_export]
macro_rules! op_successors_directive {
    ($ctx:ident, $op:ident) => {{
        let operation = $op.get_operation().deref($ctx);
        successors(operation)
    }};
}
pub use op_successors_directive;

/// Print the successors of an Operation.
pub fn successors(op: &Operation) -> OperandsList<'_, Ptr<BasicBlock>> {
    OperandsList::new("[", "]", op.successors.as_slice())
}

pub struct OperandsList<'a, K: DefUseParticipant> {
    open: &'static str,
    close: &'static str,
    list: &'a [Operand<K>],
    _marker: std::marker::PhantomData<K>,
}

impl<'a, K> OperandsList<'a, K>
where
    K: DefUseParticipant,
{
    pub fn new(open: &'static str, close: &'static str, list: &'a [Operand<K>]) -> Self {
        Self {
            open,
            close,
            list,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, K> std::ops::Deref for OperandsList<'a, K>
where
    K: DefUseParticipant,
{
    type Target = [Operand<K>];

    fn deref(&self) -> &Self::Target {
        self.list.as_ref()
    }
}

impl<'a, K> Printable for OperandsList<'a, K>
where
    K: Printable + DefUseParticipant + Named,
{
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enclosed(
            self.open,
            self.close,
            list_with_sep(self.list.as_ref(), ListSeparator::Char(',')),
        )
        .fmt(ctx, state, f)
    }
}

#[macro_export]
macro_rules! op_regions_directive {
    ($ctx:ident, $op:ident) => {{
        let operation = $op.get_operation().deref($ctx);
        regions(operation)
    }};
}
pub use op_regions_directive;

/// Print the regions of an Operation.
pub fn regions(op: &Operation) -> impl Printable + '_ {
    enclosed(
        "{",
        "}",
        list_with_sep(&op.regions, ListSeparator::Char(',')),
    )
}

#[macro_export]
macro_rules! op_region_directive {
    ($ctx:ident, $op:ident) => {
        region(*$op)
    };
}
pub use op_region_directive;

/// Print the operation name and associated symbol of the Op. The Op must implement [SymbolOpInterface].
/// The common pattern is `<opid> @<symbol_name>`. For example a function call would be printed as
/// `call @my_func`.
pub fn symb_op_header<T: Op + SymbolOpInterface>(op: &T) -> impl Printable + '_ {
    PrinterFn(
        move |ctx: &Context, _state: &State, f: &mut fmt::Formatter<'_>| {
            write!(f, "{} @{}", op.get_opid(), op.get_symbol_name(ctx))
        },
    )
}

/// Print the operation name, associated symbol and type of the Op. The Op must implement [SymbolOpInterface] and [Typed].
/// The common pattern is `<opid> @<symbol_name>: <type>`. For example a function header would
/// become `func @my_func: (i32, i32) -> i32`.
pub fn typed_symb_op_header<T: Op + SymbolOpInterface + Typed>(op: &T) -> impl Printable + '_ {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            symb_op_header(op).fmt(ctx, state, f)?;
            write!(f, ": ")?;
            Printable::fmt(&op.get_type(ctx), ctx, state, f)?;
            Ok(())
        },
    )
}

/// Print the region of an IR object that implements the [OneRegionInterface].
pub fn region<T: Op + OneRegionInterface>(op: &T) -> impl Printable + '_ {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            op.get_region(ctx).fmt(ctx, state, f)
        },
    )
}

#[macro_export]
macro_rules! op_attr_dict_directive {
    ($ctx:ident, $op:ident) => {{
        let operation = $op.get_operation().deref($ctx);
        attr_dict(operation)
    }};
}
pub use op_attr_dict_directive;

/// Print the attributes of an Op.
pub fn attr_dict(op: &Operation) -> impl Printable + '_ {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            write!(f, "{{")?;
            let attrs = op
                .attributes
                .iter()
                .map(|(k, v)| concat((quoted(k), literal(" = "), v)));
            iter_with_sep(attrs, ListSeparator::Char(',')).fmt(ctx, state, f)?;
            write!(f, "}}")
        },
    )
}

#[macro_export]
macro_rules! op_attr_directive {
    ($ctx:ident, $op:ident, $name:expr) => {{
        let operation = $op.get_operation().deref($ctx);
        attr(operation, $name)
    }};
}

pub fn attr<'op>(op: &'op Operation, name: &'static str) -> impl Printable + 'op {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            let attr = op.attributes.get(name).unwrap();
            attr.fmt(ctx, state, f)
        },
    )
}

#[macro_export]
macro_rules! op_format_directive {
    ($ctx:ident, $self:ident, $fmt:expr, $($args:expr),*) => {
        formatted(format!($fmt, $($args),*))
    };
}
pub use op_format_directive;

#[macro_export]
macro_rules! op_functional_type_directive {
    ($ctx:ident, $ty:expr, $inputs:expr, $results:expr) => {
        functional_type(print_var!(&$inputs), print_var!(&$results))
    };
}
pub use op_functional_type_directive;

/// Print a function type with inputs and results like `<(i32, i32) -> (i64)>`
pub fn functional_type<'a>(
    inputs: impl Printable + 'a,
    results: impl Printable + 'a,
) -> impl Printable + 'a {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            write!(
                f,
                "<({}) -> ({})>",
                inputs.print(ctx, state),
                results.print(ctx, state)
            )
        },
    )
}

#[macro_export]
macro_rules! op_typed_directive {
    ($self:ident) => {
        typed(*$self)
    };
}
pub use op_typed_directive;

/// Create a printer for IR entities that have a type.
pub fn typed(ty: impl IntoTypedPrinter) -> impl Printable {
    let p = ty.into_typed_printer();
    PrinterFn(move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| p.fmt(ctx, state, f))
}

pub trait IntoTypedPrinter {
    type Printer: TypedPrinter;

    fn into_typed_printer(self) -> Self::Printer;
}

impl<'a> IntoTypedPrinter for &'a dyn Type {
    type Printer = Self;
    fn into_typed_printer(self) -> Self::Printer {
        self
    }
}

impl<T: Typed + ArenaObj> IntoTypedPrinter for Ptr<T> {
    type Printer = Self;
    fn into_typed_printer(self) -> Self::Printer {
        self
    }
}

impl<I> IntoTypedPrinter for I
where
    I: IntoIterator,
    I::IntoIter: Clone,
    I::Item: Typed,
{
    type Printer = IterTypePrinter<I::IntoIter>;

    fn into_typed_printer(self) -> Self::Printer {
        IterTypePrinter(self.into_iter())
    }
}

/// Used to print the type of an IR objects that are typed.
pub trait TypedPrinter {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl<'a> TypedPrinter for &'a dyn Type {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Printable::fmt(&self, ctx, state, f)
    }
}

impl<T: Typed + ArenaObj> TypedPrinter for Ptr<T> {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let t = self.deref(ctx).get_type(ctx);
        Printable::fmt(&t, ctx, state, f)
    }
}

pub struct IterTypePrinter<I>(I);

impl<T, I> TypedPrinter for IterTypePrinter<I>
where
    I: Iterator<Item = T> + Clone,
    T: Typed,
{
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sep = ListSeparator::Char(',');
        let elems = self.0.clone().map(|ty| ty.get_type(ctx));
        iter_with_sep(elems, sep).fmt(ctx, state, f)
    }
}

/// Print an Op using the generic Operation format.
///
/// See: https://mlir.llvm.org/docs/LangRef/#operations
pub fn operation_generic_format<T: Op>(op: T) -> impl Printable {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            let op_id = op.get_opid();
            let operation = op.get_operation().deref(ctx);

            write!(f, "\"{}\"", op_id)?;

            operands(&operation).fmt(ctx, state, f)?;
            if !operation.successors.is_empty() {
                write!(f, " ")?;
                successors(&operation).fmt(ctx, state, f)?;
            }

            // MLIR would expect `dictionary properties` next.
            // We do not distinguish between attributes and properties. In fact our attributes
            // rather act as properties in MLIR. We will still print our attributes as MLIR attributes for
            // now.

            if !operation.regions.is_empty() {
                write!(f, " ")?;
                regions(&operation).fmt(ctx, state, f)?;
            }

            if !operation.attributes.is_empty() {
                write!(f, " ")?;
                attr_dict(&operation).fmt(ctx, state, f)?;
            }

            write!(f, " : ")?;

            let ty_operands = typed(&operation.operands);
            let ty_results = typed(&operation.results);
            functional_type(ty_operands, ty_results).fmt(ctx, state, f)?;

            Ok(())
        },
    )
}
