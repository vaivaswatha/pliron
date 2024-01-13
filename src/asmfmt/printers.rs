use std::fmt;

use crate::{
    common_traits::Qualified,
    context::{private::ArenaObj, Context, Ptr},
    dialects::builtin::op_interfaces::{OneRegionInterface, SymbolOpInterface},
    op::Op,
    operation::Operation,
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

pub fn qualifier<T>(v: &T) -> impl Printable + '_
where
    T: Qualified,
    <T as Qualified>::Qualifier: Printable,
{
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            v.get_qualifier(ctx).fmt(ctx, state, f)
        },
    )
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

#[macro_export]
macro_rules! operands_directive {
    ($ctx:ident, $op:ident) => {
        operands(*$op)
    };
}
#[allow(unused_imports)]
pub(crate) use operands_directive;

/// Print the operations of an Operation.
pub fn operands(op: &Operation) -> impl Printable + '_ {
    enclosed(
        "(",
        ")",
        list_with_sep(&op.operands, ListSeparator::Char(',')),
    )
}

#[macro_export]
macro_rules! successors_directive {
    ($ctx:ident, $op:ident) => {
        successors(*$op)
    };
}
#[allow(unused_imports)]
pub(crate) use successors_directive;

/// Print the successors of an Operation.
pub fn successors(op: &Operation) -> impl Printable + '_ {
    enclosed(
        "[",
        "]",
        list_with_sep(&op.successors, ListSeparator::Char(',')),
    )
}

#[macro_export]
macro_rules! regions_directive {
    ($ctx:ident, $op:ident) => {
        regions(*$op)
    };
}
#[allow(unused_imports)]
pub(crate) use regions_directive;

/// Print the regions of an Operation.
pub fn regions(op: &Operation) -> impl Printable + '_ {
    enclosed(
        "{",
        "}",
        list_with_sep(&op.regions, ListSeparator::Char(',')),
    )
}

pub fn region<T: Op + OneRegionInterface>(op: &T) -> impl Printable + '_ {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            op.get_region(ctx).fmt(ctx, state, f)
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

#[macro_export]
macro_rules! attr_dict_directive {
    ($ctx:ident, $op:ident) => {
        attr_dict(*$op)
    };
}
#[allow(unused_imports)]
pub(crate) use attr_dict_directive;

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

pub fn attr<'op>(op: &'op Operation, name: &'static str) -> impl Printable + 'op {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            let attr = op.attributes.get(name).unwrap();
            attr.fmt(ctx, state, f)
        },
    )
}

/// Print a string as a quoted string.
pub fn quoted(s: &str) -> impl Printable + '_ {
    PrinterFn(
        move |_ctx: &Context, _state: &State, f: &mut fmt::Formatter<'_>| write!(f, "{:?}", s),
    )
}

#[allow(unused_macros)]
macro_rules! format_directive {
    ($ctx:ident, $self:ident, $fmt:expr, $($args:expr),*) => {
        formatted(format!($fmt, $($args),*))
    };
}
#[allow(unused_imports)]
pub(crate) use format_directive;

/// Print a value using the given Rust format string.
///
/// Warning: formatted values are not parsable. A custom parser might need to be implemented when
/// using `formatted` in the printer.
pub fn formatted(s: String) -> impl Printable {
    PrinterFn(move |_ctx: &Context, _state: &State, f: &mut fmt::Formatter<'_>| write!(f, "{}", s))
}

#[allow(unused_macros)]
macro_rules! functional_type_directive {
    ($ctx:ident, $ty:expr, $inputs:expr, $results:expr) => {
        functional_type(print_var!(&$inputs), print_var!(&$results))
    };
}
#[allow(unused_imports)]
pub(crate) use functional_type_directive;

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

#[macro_export]
macro_rules! typed_directive {
    ($self:ident) => {
        typed(*$self)
    };
}
#[allow(unused_imports)]
pub(crate) use typed_directive;

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

/*
 * Type and Attribute directives
 * ====================================
 */

#[macro_export]
macro_rules! at_params_directive {
    ($self:ident, ($($printer:ident),*), (), ($($params:ident)*)) => {
        concat_with_sep(
            ListSeparator::Char(','),
            ($(
                ::pliron::asmfmt::printers::print_var!(&$self.$params)
            ),*),
        ).fmt($($printer),*)?;
    };
    ($_self:ident, ($($_printer:ident),*), ($($_field_name:ident)+), ($($_param:ident)*)) => {
        compile_error!("params directive used with too many parameters");
    };
}
#[allow(unused_imports)]
pub(crate) use at_params_directive;

#[macro_export]
macro_rules! at_qualifier_directive {
    ($self:ident, ($($printer:ident),*), (), ($($_param:ident)*)) => {
        qualifier($self).fmt($($printer),*)?;
    };
}
#[allow(unused_imports)]
pub(crate) use at_qualifier_directive;

#[macro_export]
macro_rules! at_qualified_directive {
    ($self:ident, ($($_printer:ident),*), (), ($($_param:tt)*)) => {
        compile_error!("qualified directive used without parameter");
    };
    ($self:ident, ($($printer:ident),*), ($field_name:tt), ($($params:tt)*)) => {
        concat((qualifier(&$self.$field_name), " ", $self.$field_name)).fmt($($printer),*)?;
    };
    ($self:ident, ($($printer:ident),*), ($field_name:tt, $($extra:tt),+), ($($params:tt)*)) => {
        compile_error!("qualified directive used with too many field names");
    };
}
#[allow(unused_imports)]
pub(crate) use at_qualified_directive;

#[macro_export]
macro_rules! at_struct_directive {
    ($self:ident, ($($printer:ident),*), ($($field_name:tt),*), ($($_param:ident)*)) => {
        concat_with_sep(
            ::pliron::printable::ListSeparator::Char(','),
            ($(
              concat((
                literal(stringify!($field_name)),
                " = ",
                ::pliron::asmfmt::printers::print_var!(&$self.$field_name),
              ))
            ),*),
        ).fmt($($printer),*)?;
    };
}
#[allow(unused_imports)]
pub(crate) use at_struct_directive;

#[allow(unused_macros)]
macro_rules! at_format_directive {
    ($self:ident, ($($printer:ident),*), (), ($($_param:ident)*)) => {
        compile_error!("format directive used without parameter");
    };
    ($self:ident, ($($printer:ident),*), ($fmt:expr, $field_name:ident), ($($params:ident)*)) => {
        formatted(format!($fmt, $self.$field_name)).fmt($($printer),*)?;
    };
    ($self:ident, ($($printer:ident),*), ($fmt:expr, $field_name:ident, $($extra:ident),+), ($($params:ident)*)) => {
        compile_error!("format directive used with too many field names");
    };
}
#[allow(unused_imports)]
pub(crate) use at_format_directive;

#[macro_export]
macro_rules! at_quoted_directive {
    ($self:ident, ($($printer:ident),*), (), ($($_param:tt)*)) => {
        compile_error!("quoted directive used without parameter");
    };
    ($self:ident, ($($printer:ident),*), ($field_name:tt), ($($params:tt)*)) => {
        quoted(&$self.$field_name).fmt($($printer),*)?;
    };
    ($self:ident, ($($printer:ident),*), ($field_name:tt, $($extra:tt),+), ($($params:tt)*)) => {
        compile_error!("quoted directive used with too many field names");
    };
}
#[allow(unused_imports)]
pub(crate) use at_quoted_directive;

/*
 * Op directives
 * =================
 */

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

#[cfg(test)]
mod tests {
    #![allow(unused)]
    #![allow(dead_code)]

    use super::*;

    use crate::{
        asmfmt::parsers::AsmParser,
        attribute::{attr_cast, Attribute},
        dialects::builtin::attr_interfaces::TypedAttrInterface,
        identifier::Identifier,
        impl_attr_interface,
        location::{self, Location},
        op::OpObj,
        parsable::{self, state_stream_from_iterator},
    };
    use apint::ApInt;
    use combine::{eof, error::Commit};
    use pliron_derive::{
        declare_op, Attribute, NotParsableAttribute, NotParsableType, Parsable, Printable, Type,
    };

    use crate::{
        asmfmt::parsers,
        attribute::AttrObj,
        common_traits::Verify,
        context::Ptr,
        error::Result,
        parsable::{Parsable, ParseResult, StateStream},
        r#type::TypeObj,
    };

    fn register_dialect(ctx: &mut Context) {
        let mut dialect = crate::dialect::Dialect::new(crate::dialect::DialectName::new("testing"));
        SimpleType::register_type_in_dialect(&mut dialect, SimpleType::parser_fn);
        IntegerType::register_type_in_dialect(&mut dialect, IntegerType::parser_fn);
        FunctionType::register_type_in_dialect(&mut dialect, FunctionType::parser_fn);
        VecType::register_type_in_dialect(&mut dialect, VecType::parser_fn);
        StringAttr::register_attr_in_dialect(&mut dialect, StringAttr::parser_fn);
        IntegerAttr::register_attr_in_dialect(&mut dialect, IntegerAttr::parser_fn);
        UnitAttr::register_attr_in_dialect(&mut dialect, UnitAttr::parser_fn);
        VecAttr::register_attr_in_dialect(&mut dialect, VecAttr::parser_fn);
        ConstantOp::register(ctx, &mut dialect, ConstantOp::parser_fn);
        dialect.register(ctx);
    }

    #[derive(Hash, PartialEq, Eq, Debug, Type, Printable, Parsable)]
    #[type_name = "testing.simple_type"]
    #[asm_format = "`()`"]
    pub struct SimpleType {}
    impl SimpleType {
        /// Get or create a new simple type.
        pub fn get(ctx: &mut Context) -> Ptr<TypeObj> {
            Type::register_instance(SimpleType {}, ctx)
        }
    }
    impl Verify for SimpleType {
        fn verify(&self, _ctx: &Context) -> Result<()> {
            Ok(())
        }
    }

    #[derive(Hash, PartialEq, Eq, Debug, Type, Printable, Parsable)]
    #[type_name = "testing.integer"]
    //#[asm_format = "`int <` `sign=` $sign `, width=` $width `, align=` $align `>`"]
    //#[asm_format = "`int <` params `>`"]
    //#[asm_format = "`int <` struct(params) `>`"]
    //#[asm_format = "`int <` struct($width, $sign) `>`"]
    #[asm_format = "`int` $width `<` $align `,` $sign `>`"]
    pub struct IntegerType {
        width: u32,
        sign: bool,
        align: u32,
    }
    impl IntegerType {
        fn get(ctx: &mut Context, width: u32, sign: bool, align: u32) -> Ptr<TypeObj> {
            Type::register_instance(Self { sign, width, align }, ctx)
        }

        /// Get, if it already exists, an integer type.
        pub fn get_existing(
            ctx: &Context,
            width: u32,
            sign: bool,
            align: u32,
        ) -> Option<Ptr<TypeObj>> {
            Type::get_instance(Self { width, sign, align }, ctx)
        }
    }
    impl Verify for IntegerType {
        fn verify(&self, _ctx: &Context) -> Result<()> {
            Ok(())
        }
    }

    #[derive(Hash, PartialEq, Eq, Debug, Type, Printable, NotParsableType)]
    #[type_name = "testing.vec"]
    #[asm_format = "`[` qualified($elem) `]` "]
    pub struct VecType {
        elem: Ptr<TypeObj>,
    }
    impl Verify for VecType {
        fn verify(&self, ctx: &Context) -> Result<()> {
            self.elem.verify(ctx)?;
            Ok(())
        }
    }

    #[derive(Hash, PartialEq, Debug, Eq, Type, Printable)]
    #[type_name = "testing.function"]
    // #[asm_format = "functional_type($inputs, $results)"]
    #[asm_format = "`(` $inputs `) -> (` $results `)`"]
    pub struct FunctionType {
        inputs: Vec<Ptr<TypeObj>>,
        results: Vec<Ptr<TypeObj>>,
    }
    impl Verify for FunctionType {
        fn verify(&self, ctx: &Context) -> Result<()> {
            for ty in &self.inputs {
                ty.verify(ctx)?;
            }
            for ty in &self.results {
                ty.verify(ctx)?;
            }
            Ok(())
        }
    }
    impl ::pliron::parsable::Parsable for FunctionType {
        type Arg = ();
        type Parsed = ::pliron::context::Ptr<::pliron::r#type::TypeObj>;
        fn parse<'a>(
            _state_stream: &mut ::pliron::parsable::StateStream<'a>,
            _arg: Self::Arg,
        ) -> ::pliron::parsable::ParseResult<'a, Self::Parsed> {
            todo!()
        }
    }

    impl FunctionType {
        pub fn get(
            ctx: &mut Context,
            inputs: Vec<Ptr<TypeObj>>,
            results: Vec<Ptr<TypeObj>>,
        ) -> Ptr<TypeObj> {
            Type::register_instance(FunctionType { inputs, results }, ctx)
        }
    }

    #[derive(PartialEq, Eq, Debug, Clone, Attribute, Printable)]
    #[attr_name = "testing.int"]
    #[asm_format = "format(`0x{:x}`, $val) `: ` $ty"]
    pub struct IntegerAttr {
        ty: Ptr<TypeObj>,
        val: ApInt,
    }
    impl IntegerAttr {
        pub fn create(ty: Ptr<TypeObj>, val: ApInt) -> AttrObj {
            Box::new(IntegerAttr { ty, val })
        }
    }
    impl Verify for IntegerAttr {
        fn verify(&self, _ctx: &Context) -> Result<()> {
            Ok(())
        }
    }
    impl ::pliron::parsable::Parsable for IntegerAttr {
        type Arg = ();
        type Parsed = ::pliron::attribute::AttrObj;
        fn parse<'a>(
            _state_stream: &mut ::pliron::parsable::StateStream<'a>,
            _arg: Self::Arg,
        ) -> ::pliron::parsable::ParseResult<'a, Self::Parsed> {
            todo!()
        }
    }
    impl_attr_interface!(TypedAttrInterface for IntegerAttr {
        fn get_type(&self) -> Ptr<TypeObj> {
            self.ty
        }
    });

    #[derive(PartialEq, Eq, Debug, Clone, Attribute, Printable, NotParsableAttribute)]
    #[attr_name = "testing.string"]
    #[asm_format = "quoted($0)"]
    struct StringAttr(String);
    impl Verify for StringAttr {
        fn verify(&self, _ctx: &Context) -> Result<()> {
            Ok(())
        }
    }

    #[derive(PartialEq, Eq, Debug, Clone, Attribute, Printable, NotParsableAttribute)]
    #[attr_name = "testing.unit"]
    #[asm_format = "`()`"]
    pub struct UnitAttr();
    impl UnitAttr {
        pub fn create() -> AttrObj {
            Box::new(UnitAttr())
        }
    }

    impl Verify for UnitAttr {
        fn verify(&self, _ctx: &Context) -> Result<()> {
            Ok(())
        }
    }

    #[derive(Clone, PartialEq, Debug, Eq, Attribute, Printable, NotParsableAttribute)]
    #[attr_name = "testing.vec"]
    pub struct VecAttr(pub Vec<AttrObj>);
    impl Verify for VecAttr {
        fn verify(&self, ctx: &Context) -> Result<()> {
            for attr in &self.0 {
                attr.verify(ctx)?;
            }
            Ok(())
        }
    }

    #[declare_op]
    #[op_name = "testing.const"]
    #[derive(Printable)]
    struct ConstantOp;
    impl ConstantOp {
        /// Attribute key for the constant value.
        pub const ATTR_KEY_VALUE: &'static str = "constant.value";

        /// Get the constant value that this Op defines.
        pub fn get_value(&self, ctx: &Context) -> AttrObj {
            let op = self.get_operation().deref(ctx);
            op.attributes.get(Self::ATTR_KEY_VALUE).unwrap().clone()
        }

        /// Create a new [ConstantOp]. The underlying [Operation] is not linked to a [BasicBlock].
        pub fn new_unlinked(ctx: &mut Context, value: AttrObj) -> Self {
            let result_type = attr_cast::<dyn TypedAttrInterface>(&*value)
                .expect("ConstantOp const value must provide TypedAttrInterface")
                .get_type();
            let op = Operation::new(ctx, Self::get_opid_static(), vec![result_type], vec![], 0);
            op.deref_mut(ctx)
                .attributes
                .insert(Self::ATTR_KEY_VALUE, value);
            Self { op }
        }
    }
    impl Verify for ConstantOp {
        fn verify(&self, _ctx: &Context) -> Result<()> {
            Ok(())
        }
    }
    impl Parsable for ConstantOp {
        type Arg = Vec<(Identifier, Location)>;
        type Parsed = OpObj;

        fn parse<'a>(
            _state_stream: &mut StateStream<'a>,
            _arg: Self::Arg,
        ) -> ParseResult<'a, Self::Parsed> {
            todo!()
        }
    }

    #[test]
    fn print_simple_type() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let got = SimpleType::get(&mut ctx).disp(&ctx).to_string();
        assert_eq!(got, "()");
    }

    #[test]
    fn print_integer_type() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let ty = IntegerType::get(&mut ctx, 32, true, 8);
        let got = ty.disp(&ctx).to_string();
        assert_eq!(got, "int32<8,true>");
    }

    #[test]
    #[ignore]
    fn parse_integer_type() {
        use combine::Parser;

        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        // TODO:
        let a = "testing.integer<sign=true, width=32, align=8>".to_string();
        let mut state_stream = state_stream_from_iterator(
            a.chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let _ = parsers::type_header()
            .parse_next(&mut state_stream)
            .unwrap();
        let res = IntegerType::parser(())
            .and(eof())
            .parse(state_stream)
            .unwrap()
            .0
             .0;

        assert!(res == IntegerType::get_existing(&ctx, 32, true, 8).unwrap());
    }

    #[test]
    fn print_vec_type() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let i32_ty = IntegerType::get(&mut ctx, 32, true, 4);
        let vec_ty = VecType { elem: i32_ty };
        let got = vec_ty.disp(&ctx).to_string();
        assert_eq!(got, "[testing.integer int32<4,true>]");
    }

    #[test]
    fn print_function() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let i32_ty = IntegerType::get(&mut ctx, 32, true, 4);
        let u64_ty = IntegerType::get(&mut ctx, 32, false, 8);
        let func_ty = FunctionType::get(&mut ctx, vec![i32_ty, i32_ty], vec![u64_ty]);

        let got = func_ty.disp(&ctx).to_string();
        assert_eq!(got, "(int32<4,true>,int32<4,true>) -> (int32<8,false>)");
    }

    #[test]
    fn print_unit_attr() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let attr = UnitAttr();
        let got = attr.disp(&ctx).to_string();
        assert_eq!(got, "()");
    }

    #[test]
    fn print_string_attr() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let attr = StringAttr("hello".to_string());
        let got = attr.disp(&ctx).to_string();
        assert_eq!(got, r#""hello""#);
    }

    #[test]
    fn print_int_attr() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let ty = IntegerType::get(&mut ctx, 32, true, 8);
        let attr = IntegerAttr {
            ty,
            val: ApInt::from(42),
        };
        let got = attr.disp(&ctx).to_string();
        assert_eq!(got, "0x2a: int32<8,true>");
    }

    #[test]
    fn print_vec_attr() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let vec_attr = VecAttr(vec![UnitAttr::create(), UnitAttr::create()]);
        let got = vec_attr.disp(&ctx).to_string();
        assert_eq!(got, "<(),()>");
    }

    #[test]
    fn print_const_op() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let i32_ty = IntegerType::get(&mut ctx, 32, true, 4);
        let const_value = ApInt::from(42);

        let const_op = ConstantOp::new_unlinked(&mut ctx, IntegerAttr::create(i32_ty, const_value));

        let got = const_op.disp(&ctx).to_string();
        assert_eq!(
            got,
            r#"op_0_0_res0 = "testing.const"() {"constant.value" = 0x2a: int32<4,true>} : <() -> (int32<4,true>)>"#
        );
    }
}
