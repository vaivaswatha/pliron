//!
//! Op directives
//! ==============
//!

use std::fmt;

use crate::{
    basic_block::BasicBlock,
    common_traits::Named,
    context::{private::ArenaObj, Context, Ptr},
    dialects::builtin::op_interfaces::OneRegionInterface,
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
        operation_generic_format(*$self)
    };
}
#[allow(unused_imports)]
pub(crate) use op_operation_generic_format_directive;

#[macro_export]
macro_rules! op_results_directive {
    ($ctx:ident, $op:ident) => {
        &($op.get_operation().deref($ctx).results)
    };
}
#[allow(unused_imports)]
pub(crate) use op_results_directive;

#[macro_export]
macro_rules! op_check_directive {
    ($ctx:ident, $self:ident, $ty:expr) => {
        check($ctx, $ty)
    };
}
#[allow(unused_imports)]
pub(crate) use op_check_directive;

#[macro_export]
macro_rules! op_operands_directive {
    ($ctx:ident, $op:ident) => {{
        let operation = $op.get_operation().deref($ctx);
        OperandsList::new("(", ")", &operation.operands)
    }};
}
#[allow(unused_imports)]
pub(crate) use op_operands_directive;

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
#[allow(unused_imports)]
pub(crate) use op_successors_directive;

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
#[allow(unused_imports)]
pub(crate) use op_regions_directive;

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
#[allow(unused_imports)]
pub(crate) use op_region_directive;

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
#[allow(unused_imports)]
pub(crate) use op_attr_dict_directive;

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

#[allow(unused_macros)]
macro_rules! op_format_directive {
    ($ctx:ident, $self:ident, $fmt:expr, $($args:expr),*) => {
        formatted(format!($fmt, $($args),*))
    };
}
#[allow(unused_imports)]
pub(crate) use op_format_directive;

#[allow(unused_macros)]
macro_rules! op_functional_type_directive {
    ($ctx:ident, $ty:expr, $inputs:expr, $results:expr) => {
        functional_type(print_var!(&$inputs), print_var!(&$results))
    };
}
#[allow(unused_imports)]
pub(crate) use op_functional_type_directive;

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
#[allow(unused_imports)]
pub(crate) use op_typed_directive;

pub fn typed(ty: impl TypedPrinter) -> impl Printable {
    PrinterFn(move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| ty.fmt(ctx, state, f))
}

/// Used to print the type of an IR object.
pub trait TypedPrinter {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl TypedPrinter for dyn Type {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Printable::fmt(self, ctx, state, f)
    }
}

impl<T: TypedPrinter> TypedPrinter for &T {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self).fmt(ctx, state, f)
    }
}

impl<T: Typed + ArenaObj> TypedPrinter for Ptr<T> {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let t = self.deref(ctx).get_type(ctx);
        Printable::fmt(&t, ctx, state, f)
    }
}

impl<T: Typed> TypedPrinter for &Vec<T> {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sep = ListSeparator::Char(',');
        let elems = self.iter().map(|ty| ty.get_type(ctx));
        iter_with_sep(elems, sep).fmt(ctx, state, f)
    }
}

impl<T: Typed> TypedPrinter for &[T] {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sep = ListSeparator::Char(',');
        let elems = self.iter().map(|ty| ty.get_type(ctx));
        iter_with_sep(elems, sep).fmt(ctx, state, f)
    }
}
