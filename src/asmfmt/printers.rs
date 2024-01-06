use std::fmt;

use crate::{
    attribute::{Attribute, AttributeDict},
    basic_block::BasicBlock,
    context::{Context, Ptr},
    op::Op,
    operation::Operand,
    printable::{fmt_iter, ListSeparator, Printable, State},
    r#type::{Type, Typed},
    region::Region,
    use_def_lists::Value,
};

struct PrinterFn<F>(F);

impl<F> Printable for PrinterFn<F>
where
    F: Fn(&Context, &State, &mut fmt::Formatter<'_>) -> fmt::Result,
{
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0)(ctx, state, f)
    }
}

pub fn type_header<T: Type>(ty: &T) -> impl Printable + '_ {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            ty.get_type_id().fmt(ctx, state, f)
        },
    )
}

pub fn attr_header<T: Attribute>(attr: &T) -> impl Printable + '_ {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            attr.get_attr_id().fmt(ctx, state, f)
        },
    )
}

pub fn disp(disp: impl fmt::Display) -> impl Printable {
    PrinterFn(
        move |_ctx: &Context, _state: &State, f: &mut fmt::Formatter<'_>| write!(f, "{}", disp),
    )
}

pub fn literal(lit: &str) -> impl Printable + '_ {
    disp(lit)
}

pub fn list_with_sep<T: Printable>(items: &[T], sep: ListSeparator) -> impl Printable + '_ {
    iter_with_sep(items.iter(), sep)
}

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

fn operands(ops: &[Operand<Value>]) -> impl Printable + '_ {
    let sep = ListSeparator::Char(',');
    concat(("(", list_with_sep(ops, sep), ")"))
}

fn successors(succs: &[Operand<Ptr<BasicBlock>>]) -> impl Printable + '_ {
    let sep = ListSeparator::Char(',');
    concat(("[", list_with_sep(succs, sep), "]"))
}

fn regions(rs: &[Ptr<Region>]) -> impl Printable + '_ {
    let sep = ListSeparator::Char(',');
    concat(("{", list_with_sep(rs, sep), "}"))
}

#[macro_export]
macro_rules! attr_dict_directive {
    ($op:ident) => {
        attr_dict_op(*$op)
    };
}
#[allow(unused_imports)]
pub(crate) use attr_dict_directive;

fn attr_dict_op<T: Op + Copy>(op: T) -> impl Printable {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            let op = op.get_operation().deref(ctx);
            fmt_attr_dict(&op.attributes, ctx, state, f)
        },
    )
}

fn attr_dict(attrs: &AttributeDict) -> impl Printable + '_ {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            fmt_attr_dict(attrs, ctx, state, f)
        },
    )
}

fn fmt_attr_dict(
    attrs: &AttributeDict,
    ctx: &Context,
    state: &State,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    write!(f, "{{")?;
    let attrs = attrs
        .iter()
        .map(|(k, v)| concat((quoted(k), literal(" = "), v)));
    iter_with_sep(attrs, ListSeparator::Char(',')).fmt(ctx, state, f)?;
    write!(f, "}}")
}

#[macro_export]
macro_rules! quoted_directive {
    ($self:ident, $ty:expr) => {
        quoted(&($ty))
    };
}
#[allow(unused_imports)]
pub(crate) use quoted_directive;

fn quoted(s: &str) -> impl Printable + '_ {
    PrinterFn(
        move |_ctx: &Context, _state: &State, f: &mut fmt::Formatter<'_>| write!(f, "{:?}", s),
    )
}

#[allow(unused_macros)]
macro_rules! format_directive {
    ($self:ident, $fmt:expr, $($args:expr),*) => {
        formatted(format!($fmt, $($args),*))
    };
}
#[allow(unused_imports)]
pub(crate) use format_directive;

pub fn formatted(s: String) -> impl Printable {
    PrinterFn(move |_ctx: &Context, _state: &State, f: &mut fmt::Formatter<'_>| write!(f, "{}", s))
}

#[allow(unused_macros)]
macro_rules! function_type_directive {
    ($ty:expr, $inputs:expr, $results:expr) => {
        function_type(print_var!(&$inputs), print_var!(&$results))
    };
}
#[allow(unused_imports)]
pub(crate) use function_type_directive;

pub fn function_type<'a>(
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
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| items.fmt(ctx, state, f),
    )
}

// locally typed alias for to capture and print a comma separated list of attributes via tuples.
pub trait PrinterList {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result;
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
      fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
          self.0.fmt(ctx, state, f)?;
          printer_list_tuple_trait_cont!(1, self, ctx, state, f, $($id)+);
          Ok(())
      }
    }
  );
);

// Implement body part of PrinterList trait iterating over all elements self (the tuple input).
macro_rules! printer_list_tuple_trait_cont(
  ($idx:tt, $self:expr, $ctx:expr, $state:expr, $f:expr, $head:ident $($id:ident)+) => (
    write!($f, ", ")?;
    $self.$idx.fmt($ctx, $state, $f)?;
    succ!($idx, printer_list_tuple_trait_cont!($self, $ctx, $state, $f, $($id)+))
  );
  ($idx:expr, $self:expr, $ctx:expr, $state:expr, $f:expr, $head:ident) => (
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
macro_rules! generic_op_format_directive {
    ($self:ident) => {
        generic_op_format(*$self)
    };
}
#[allow(unused_imports)]
pub(crate) use generic_op_format_directive;

pub fn generic_op_format<T: Op + Copy>(op: T) -> impl Printable {
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            fmt_generic_op_format(op, ctx, state, f)
        },
    )
}

#[macro_export]
macro_rules! type_directive {
    ($self:ident) => {
        typed(*$self)
    };
}

pub fn typed(ty: impl TypedListPrinter) -> impl Printable {
    PrinterFn(move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| ty.fmt(ctx, state, f))
}

pub trait TypedListPrinter {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl<T: TypedListPrinter> TypedListPrinter for &T {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self).fmt(ctx, state, f)
    }
}

impl<T: Typed> TypedListPrinter for &Vec<T> {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sep = ListSeparator::Char(',');
        let elems = self.iter().map(|ty| ty.get_type(ctx));
        iter_with_sep(elems, sep).fmt(ctx, state, f)
    }
}

impl<T: Typed> TypedListPrinter for &[T] {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sep = ListSeparator::Char(',');
        let elems = self.iter().map(|ty| ty.get_type(ctx));
        iter_with_sep(elems, sep).fmt(ctx, state, f)
    }
}

// https://mlir.llvm.org/docs/LangRef/#operations
pub fn fmt_generic_op_format<T: Op>(
    op: T,
    ctx: &Context,
    state: &State,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    let op_id = op.get_opid();
    let op = op.get_operation().deref(ctx);

    write!(f, "\"{}\"", op_id)?;

    operands(&op.operands).fmt(ctx, state, f)?;

    if !op.successors.is_empty() {
        write!(f, " ")?;
        successors(&op.successors).fmt(ctx, state, f)?;
    }

    // MLIR would expect `dictionary properties` next.
    // We do not distinguish between attributes and properties. In fact our attributes
    // rather act as properties in MLIR. We will still print our attributes as MLIR attributes for
    // now.

    if !op.regions.is_empty() {
        write!(f, " ")?;
        regions(&op.regions).fmt(ctx, state, f)?;
    }

    if !op.attributes.is_empty() {
        write!(f, " ")?;
        fmt_attr_dict(&op.attributes, ctx, state, f)?;
    }

    write!(f, " : ")?;

    // todo: function type
    // function_type(todo!(), todo!()).fmt(ctx, state, f)?;

    let ty_operands = typed(&op.operands);
    let ty_results = typed(&op.results);
    function_type(ty_operands, ty_results).fmt(ctx, state, f)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        asmfmt::parsers::AsmParser,
        location,
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
        r#type::{TypeId, TypeObj},
    };

    fn register_dialect(ctx: &mut Context) {
        let mut dialect = crate::dialect::Dialect::new(crate::dialect::DialectName::new("testing"));
        SimpleType::register_type_in_dialect(&mut dialect, SimpleType::parser_fn);
        IntegerType::register_type_in_dialect(&mut dialect, IntegerType::parser_fn);
        FunctionType::register_type_in_dialect(&mut dialect, FunctionType::parser_fn);
        StringAttr::register_attr_in_dialect(&mut dialect, StringAttr::parser_fn);
        IntegerAttr::register_attr_in_dialect(&mut dialect, IntegerAttr::parser_fn);
        UnitAttr::register_attr_in_dialect(&mut dialect, UnitAttr::parser_fn);
        VecAttr::register_attr_in_dialect(&mut dialect, VecAttr::parser_fn);
        dialect.register(ctx);
    }

    #[derive(Hash, PartialEq, Eq, Debug, Type, Printable)]
    #[type_name = "testing.simple_type"]
    // #[asm_format = ""]
    pub struct SimpleType {}
    impl SimpleType {
        /// Get or create a new simple type.
        pub fn get(ctx: &mut Context, _id: TypeId) -> Ptr<TypeObj> {
            Type::register_instance(SimpleType {}, ctx)
        }
    }
    impl Verify for SimpleType {
        fn verify(&self, _ctx: &Context) -> Result<()> {
            Ok(())
        }
    }
    impl Parsable for SimpleType {
        type Arg = ();
        type Parsed = Ptr<TypeObj>;

        fn parse<'a>(
            state_stream: &mut StateStream<'a>,
            _arg: Self::Arg,
        ) -> ParseResult<'a, Self::Parsed> {
            let id = parsers::type_header().parse_next(state_stream)?.0;
            Ok((
                SimpleType::get(state_stream.state.ctx, id),
                Commit::Commit(()),
            ))
        }
    }

    #[derive(Hash, PartialEq, Eq, Debug, Type, Printable, Parsable)]
    #[type_name = "testing.integer"]
    //#[asm_format = "`<` `sign=` $sign `, width=` $width `, align=` $align `>`"]
    pub struct IntegerType {
        sign: bool,
        width: u32,
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

    #[derive(Hash, PartialEq, Debug, Eq, Type, Printable, NotParsableType)]
    #[type_name = "testing.function"]
    #[asm_format = "function_type($inputs, $results)"]
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

    impl FunctionType {
        pub fn get(
            ctx: &mut Context,
            inputs: Vec<Ptr<TypeObj>>,
            results: Vec<Ptr<TypeObj>>,
        ) -> Ptr<TypeObj> {
            Type::register_instance(FunctionType { inputs, results }, ctx)
        }
    }

    #[derive(PartialEq, Eq, Debug, Clone, Attribute, Printable, NotParsableAttribute)]
    #[attr_name = "testing.integer"]
    #[asm_format = "` <` format(`0x{:x}`, $val) `: ` $ty `>`"]
    pub struct IntegerAttr {
        ty: Ptr<TypeObj>,
        val: ApInt,
    }
    impl Verify for IntegerAttr {
        fn verify(&self, _ctx: &Context) -> Result<()> {
            Ok(())
        }
    }

    #[derive(PartialEq, Eq, Debug, Clone, Attribute, Printable, NotParsableAttribute)]
    #[attr_name = "testing.string"]
    #[asm_format = "` ` quoted($0)"]
    struct StringAttr(String);
    impl Verify for StringAttr {
        fn verify(&self, _ctx: &Context) -> Result<()> {
            Ok(())
        }
    }

    #[derive(PartialEq, Eq, Debug, Clone, Attribute, Printable, NotParsableAttribute)]
    #[attr_name = "testing.unit"]
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
    #[op_name = "testing.op"]
    #[derive(Printable)]
    struct MyOp;
    impl Verify for MyOp {
        fn verify(&self, _ctx: &Context) -> Result<()> {
            Ok(())
        }
    }

    #[test]
    fn print_simple_type() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let got = SimpleType {}.disp(&ctx).to_string();
        assert_eq!(got, "testing.simple_type");
    }

    #[test]
    fn print_integer_type() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let ty = IntegerType::get(&mut ctx, 32, true, 8);
        let got = ty.disp(&ctx).to_string();
        assert_eq!(got, "testing.integer<sign=true, width=32, align=8>");
    }

    #[test]
    fn parse_integer_type() {
        use combine::Parser;

        let mut ctx = Context::new();
        register_dialect(&mut ctx);

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
    fn print_function() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let i32_ty = IntegerType::get(&mut ctx, 32, true, 4);
        let u64_ty = IntegerType::get(&mut ctx, 32, false, 8);
        let func_ty = FunctionType::get(&mut ctx, vec![i32_ty, i32_ty], vec![u64_ty]);

        let got = func_ty.disp(&ctx).to_string();
        assert_eq!(
            got,
            "testing.function<(testing.integer<sign=true, width=32, align=4>,testing.integer<sign=true, width=32, align=4>) -> (testing.integer<sign=false, width=32, align=8>)>"
        );
    }

    #[test]
    fn print_unit_attr() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let attr = UnitAttr();
        let got = attr.disp(&ctx).to_string();
        assert_eq!(got, "testing.unit");
    }

    #[test]
    fn print_string_attr() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let attr = StringAttr("hello".to_string());
        let got = attr.disp(&ctx).to_string();
        assert_eq!(got, "testing.string \"hello\"");
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
        assert_eq!(
            got,
            "testing.integer <0x2a: testing.integer<sign=true, width=32, align=8>>"
        );
    }

    #[test]
    fn print_vec_attr() {
        let mut ctx = Context::new();
        register_dialect(&mut ctx);

        let vec_attr = VecAttr(vec![UnitAttr::create(), UnitAttr::create()]);
        let got = vec_attr.disp(&ctx).to_string();
        assert_eq!(got, "testing.vec <testing.unit,testing.unit>");
    }
}
