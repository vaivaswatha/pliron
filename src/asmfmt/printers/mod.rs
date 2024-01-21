//! Printers for IR objects.
//!
//! This module provides a set of reusable printer for IR objects.
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

/// Print a list of items separated by [sep].
pub fn list_with_sep<T: Printable>(items: &[T], sep: ListSeparator) -> impl Printable + '_ {
    iter_with_sep(items.iter(), sep)
}

/// Print an iterator of items separated by [sep].
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
pub fn typed(ty: impl TypedPrinter) -> impl Printable {
    PrinterFn(move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| ty.fmt(ctx, state, f))
}

/// Used to print the type of an IR objects that are typed.
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
