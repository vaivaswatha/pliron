//! Printers for IR objects.
//!
//! This module provides a set of reusable printers for IR objects.
//! The printers are also used by the Printable derive macro.

use std::fmt;

pub mod op;

use crate::{
    context::{private::ArenaObj, Context, Ptr},
    printable::{fmt_iter, ListSeparator, Printable, State},
    r#type::{Type, Typed},
};

/// Wrap a function to implement the Printable trait
struct PrinterFn<F>(F);

impl<F> Printable for PrinterFn<F>
where
    F: Fn(&Context, &State, &mut fmt::Formatter<'_>) -> fmt::Result,
{
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0)(ctx, state, f)
    }
}

/// Print a value that implements Display.
pub fn disp(disp: impl fmt::Display) -> impl Printable {
    PrinterFn(
        move |_ctx: &Context, _state: &State, f: &mut fmt::Formatter<'_>| write!(f, "{}", disp),
    )
}

/// Print a plain string as is.
pub fn literal(lit: &str) -> impl Printable + '_ {
    disp(lit)
}

/// Print a string as a quoted string.
pub fn quoted(s: &str) -> impl Printable + '_ {
    PrinterFn(
        move |_ctx: &Context, _state: &State, f: &mut fmt::Formatter<'_>| write!(f, "{:?}", s),
    )
}

/// Print a value using the given Rust format string.
///
/// Warning: formatted values are not parsable. A custom parser might need to be implemented when
/// using `formatted` in the printer.
pub fn formatted(s: String) -> impl Printable {
    PrinterFn(move |_ctx: &Context, _state: &State, f: &mut fmt::Formatter<'_>| write!(f, "{}", s))
}

/// Print a list of items separated by `sep`.
pub fn list_with_sep<T: Printable>(items: &[T], sep: ListSeparator) -> impl Printable + '_ {
    iter_with_sep(items.iter(), sep)
}

/// Print an iterator of items separated by `sep`.
pub fn iter_with_sep<I>(iter: I, sep: ListSeparator) -> impl Printable
where
    I: Iterator + Clone,
    I::Item: Printable,
{
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            fmt_iter(iter.clone(), ctx, state, sep, f)
        },
    )
}

/// Print `p` enclosed by `left` and `right`.
pub fn enclosed<P: Printable>(left: &'static str, right: &'static str, p: P) -> impl Printable {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            write!(f, "{}", left)?;
            p.fmt(ctx, state, f)?;
            write!(f, "{}", right)
        },
    )
}

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

/// Used to print the type of IR objects that are typed.
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
