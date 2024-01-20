use std::fmt;

use crate::{
    context::{private::ArenaObj, Context, Ptr},
    dialects::builtin::op_interfaces::SymbolOpInterface,
    op::Op,
    printable::{fmt_iter, ListSeparator, Printable, State},
};

mod attrtype;
#[allow(unused_imports)]
pub use attrtype::*;

mod op;
pub use op::*;

#[cfg(test)]
mod tests;

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

pub fn symb_op_header<T: Op + SymbolOpInterface>(op: &T) -> impl Printable + '_ {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            concat((op.get_opid(), " @", op.get_symbol_name(ctx))).fmt(ctx, state, f)
        },
    )
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

// Using autoref specialization to find a printer implementation for different
// kind of input types.
//
// Specialization order:
// 1. T implements Printable
// 2. T is a collection of Printable
// 3. T implements Display
//
// Autoref specialization idea is explained by dtolnay at:
//   https://github.com/dtolnay/case-studies/blob/master/autoref-specialization/README.md
#[macro_export]
macro_rules! print_var {
    ($v:expr) => {{
        #[allow(unused_imports)]
        use $crate::asmfmt::printers::{DisplayKind, PrintableIterKind, PrintableKind};
        match $v {
            v => (&v).var_kind().build(v),
        }
    }};
}

// make macro available in this crate;
#[allow(unused_imports)]
pub(crate) use print_var;

pub struct DisplayVar<T>(T);

impl<T: fmt::Display> Printable for DisplayVar<T> {
    fn fmt(&self, _ctx: &Context, _state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub struct PrintableVar<T>(T);

impl<T: Printable> Printable for PrintableVar<T> {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(ctx, state, f)
    }
}

pub struct PrintableIterVar<T, L>(L, std::marker::PhantomData<T>);

impl<T: Printable, L: AsRef<[T]>> Printable for PrintableIterVar<T, L> {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        list_with_sep(self.0.as_ref(), ListSeparator::Char(',')).fmt(ctx, state, f)
    }
}

// returned by var! if the variable implements Display, but not Printable.
pub struct DisplayTag;
impl<T: fmt::Display> DisplayKind for &&T {}
trait DisplayKind {
    #[inline]
    fn var_kind(&self) -> DisplayTag {
        DisplayTag
    }
}
impl DisplayTag {
    pub fn build<T: fmt::Display>(self, v: T) -> DisplayVar<T> {
        DisplayVar(v)
    }
}

pub struct PrintableIterTag<T>(std::marker::PhantomData<T>);
impl<T: Printable> PrintableIterKind<T> for &Vec<T> {}

trait PrintableIterKind<T> {
    #[inline]
    fn var_kind(&self) -> PrintableIterTag<T> {
        PrintableIterTag(std::marker::PhantomData)
    }
}
impl<T: Printable> PrintableIterTag<T> {
    pub fn build<L: AsRef<[T]>>(self, v: L) -> PrintableIterVar<T, L> {
        PrintableIterVar(v, std::marker::PhantomData)
    }
}

pub struct PrintableTag;
impl<T: Printable> PrintableKind for T {}
trait PrintableKind {
    #[inline]
    fn var_kind(&self) -> PrintableTag {
        PrintableTag
    }
}
impl PrintableTag {
    pub fn build<T: Printable>(self, v: T) -> PrintableVar<T> {
        PrintableVar(v)
    }
}

/// Concatenate a heterogeneous list of printable items.
///
/// For example this will create a printer that prints "foobar":
///
///   concat((disp("foo"), disp("bar")))
///
/// The `PrinterList` type argument is a tuple of printers.
pub fn concat<List: PrinterList>(items: List) -> impl Printable {
    concat_with_sep(ListSeparator::None, items)
}

pub fn concat_with_sep<List: PrinterList>(sep: ListSeparator, items: List) -> impl Printable {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            items.fmt(ctx, state, sep, f)
        },
    )
}

pub fn enclosed<P: Printable>(left: &'static str, right: &'static str, p: P) -> impl Printable {
    concat((literal(left), p, literal(right)))
}

// locally typed alias for to capture and print a comma separated list of attributes via tuples.
pub trait PrinterList {
    fn fmt(
        &self,
        ctx: &Context,
        state: &State,
        sep: ListSeparator,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result;
}

// we use succ to increment the tuple index in our macros.
macro_rules! succ (
  (0, $submac:ident ! ($($rest:tt)*)) => ($submac!(1, $($rest)*));
  (1, $submac:ident ! ($($rest:tt)*)) => ($submac!(2, $($rest)*));
  (2, $submac:ident ! ($($rest:tt)*)) => ($submac!(3, $($rest)*));
  (3, $submac:ident ! ($($rest:tt)*)) => ($submac!(4, $($rest)*));
  (4, $submac:ident ! ($($rest:tt)*)) => ($submac!(5, $($rest)*));
  (5, $submac:ident ! ($($rest:tt)*)) => ($submac!(6, $($rest)*));
  (6, $submac:ident ! ($($rest:tt)*)) => ($submac!(7, $($rest)*));
  (7, $submac:ident ! ($($rest:tt)*)) => ($submac!(8, $($rest)*));
  (8, $submac:ident ! ($($rest:tt)*)) => ($submac!(9, $($rest)*));
  (9, $submac:ident ! ($($rest:tt)*)) => ($submac!(10, $($rest)*));
  (10, $submac:ident ! ($($rest:tt)*)) => ($submac!(11, $($rest)*));
  (11, $submac:ident ! ($($rest:tt)*)) => ($submac!(12, $($rest)*));
  (12, $submac:ident ! ($($rest:tt)*)) => ($submac!(13, $($rest)*));
  (13, $submac:ident ! ($($rest:tt)*)) => ($submac!(14, $($rest)*));
  (14, $submac:ident ! ($($rest:tt)*)) => ($submac!(15, $($rest)*));
  (15, $submac:ident ! ($($rest:tt)*)) => ($submac!(16, $($rest)*));
  (16, $submac:ident ! ($($rest:tt)*)) => ($submac!(17, $($rest)*));
  (17, $submac:ident ! ($($rest:tt)*)) => ($submac!(18, $($rest)*));
  (18, $submac:ident ! ($($rest:tt)*)) => ($submac!(19, $($rest)*));
  (19, $submac:ident ! ($($rest:tt)*)) => ($submac!(20, $($rest)*));
  (20, $submac:ident ! ($($rest:tt)*)) => ($submac!(21, $($rest)*));
);

// Macro to create PrinterList for tuples of attributes.
// This macro iterates over all tuple lengths creating implementations for all supported tuple
// sizes.
macro_rules! printer_list_tuple_trait(
  ($first:ident $second:ident $($id: ident)+) => (
    printer_list_tuple_trait!(__impl $first $second; $($id)+);
  );
  (__impl $($current:ident)*; $head:ident $($id: ident)+) => (
    printer_list_tuple_trait_impl!($($current)*);

    printer_list_tuple_trait!(__impl $($current)* $head; $($id)+);
  );
  (__impl $($current:ident)*; $head:ident) => (
    printer_list_tuple_trait_impl!($($current)*);
    printer_list_tuple_trait_impl!($($current)* $head);
  );
);

// Create trait implementation for current tuple configuration
macro_rules! printer_list_tuple_trait_impl(
  ($($id:ident)+) => (
    impl<$($id: Printable),+> PrinterList for ($($id,)+) {
      fn fmt(&self, ctx: &Context, state: &State, sep: ListSeparator, f: &mut fmt::Formatter<'_>) -> fmt::Result {
          self.0.fmt(ctx, state, f)?;
          printer_list_tuple_trait_cont!(1, self, ctx, state, sep, f, $($id)+);
          Ok(())
      }
    }
  );
);

// Implement body part of PrinterList trait iterating over all elements self (the tuple input).
macro_rules! printer_list_tuple_trait_cont(
  ($idx:tt, $self:expr, $ctx:expr, $state:expr, $sep:expr, $f:expr, $head:ident $($id:ident)+) => (
    $sep.fmt($ctx, $state, $f)?;
    $self.$idx.fmt($ctx, $state, $f)?;
    succ!($idx, printer_list_tuple_trait_cont!($self, $ctx, $state, $sep, $f, $($id)+))
  );
  ($idx:expr, $self:expr, $ctx:expr, $state:expr, $sep:expr, $f:expr, $head:ident) => (
  );
);

printer_list_tuple_trait!(A B C D E F G H I J K L M N O P Q R S T);

#[macro_export]
macro_rules! get_attr {
    ($self:ident, $name:expr) => {
        todo!()
    };
}
#[allow(unused_imports)]
pub(crate) use get_attr;

pub fn check(ctx: &Context, v: impl PrinterCheck) -> bool {
    v.check(ctx)
}

pub trait PrinterCheck {
    fn check(&self, ctx: &Context) -> bool;
}

impl PrinterCheck for bool {
    fn check(&self, _ctx: &Context) -> bool {
        *self
    }
}

impl<T: PrinterCheck> PrinterCheck for &T {
    fn check(&self, ctx: &Context) -> bool {
        (*self).check(ctx)
    }
}

impl<T: PrinterCheck> PrinterCheck for Box<T> {
    fn check(&self, ctx: &Context) -> bool {
        (**self).check(ctx)
    }
}

impl<T: PrinterCheck> PrinterCheck for Option<T> {
    fn check(&self, ctx: &Context) -> bool {
        match self {
            Some(v) => v.check(ctx),
            None => false,
        }
    }
}

impl<T> PrinterCheck for Vec<T> {
    fn check(&self, _ctx: &Context) -> bool {
        !self.is_empty()
    }
}

impl<T: PrinterCheck + ArenaObj> PrinterCheck for Ptr<T> {
    fn check(&self, ctx: &Context) -> bool {
        self.deref(ctx).check(ctx)
    }
}
