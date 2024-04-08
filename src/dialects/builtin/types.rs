use combine::{
    between, choice, many1,
    parser::{char::digit, char::string},
    token, Parser,
};
use pliron_derive::def_type;

use crate::{
    common_traits::Verify,
    context::{Context, Ptr},
    dialect::Dialect,
    error::Result,
    impl_verify_succ,
    irfmt::{
        parsers::{delimited_list_parser, spaced, type_parser},
        printers::{functional_type, list_with_sep},
    },
    parsable::{IntoParseResult, Parsable, ParseResult, StateStream},
    printable::{self, ListSeparator, Printable},
    r#type::{Type, TypeObj, TypePtr},
};

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Signedness {
    Signed,
    Unsigned,
    Signless,
}

#[def_type("builtin.int")]
#[derive(Hash, PartialEq, Eq, Debug)]
pub struct IntegerType {
    width: u64,
    signedness: Signedness,
}

impl IntegerType {
    /// Get or create a new integer type.
    pub fn get(ctx: &mut Context, width: u64, signedness: Signedness) -> TypePtr<Self> {
        Type::register_instance(IntegerType { width, signedness }, ctx)
    }
    /// Get, if it already exists, an integer type.
    pub fn get_existing(
        ctx: &Context,
        width: u64,
        signedness: Signedness,
    ) -> Option<TypePtr<Self>> {
        Type::get_instance(IntegerType { width, signedness }, ctx)
    }

    /// Get width.
    pub fn get_width(&self) -> u64 {
        self.width
    }

    /// Get signedness.
    pub fn get_signedness(&self) -> Signedness {
        self.signedness
    }
}

impl Parsable for IntegerType {
    type Arg = ();
    type Parsed = TypePtr<Self>;
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        // Choose b/w si/ui/i ...
        let choicer = choice((
            string("si").map(|_| Signedness::Signed),
            string("ui").map(|_| Signedness::Unsigned),
            string("i").map(|_| Signedness::Signless),
        ));

        // followed by an integer.
        let parser = choicer
            .and(many1::<String, _, _>(digit()).map(|digits| digits.parse::<u64>().unwrap()));

        let mut parser = between(token('<'), token('>'), spaced(parser));
        parser
            .parse_stream(&mut state_stream.stream)
            .map(|(signedness, width)| IntegerType::get(state_stream.state.ctx, width, signedness))
            .into()
    }
}

impl Printable for IntegerType {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "<",)?;
        match &self.signedness {
            Signedness::Signed => write!(f, "si{}", self.width)?,
            Signedness::Unsigned => write!(f, "ui{}", self.width)?,
            Signedness::Signless => write!(f, "i{}", self.width)?,
        }
        write!(f, ">")
    }
}

impl Verify for IntegerType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        todo!()
    }
}

/// Map from a list of inputs to a list of results
///
/// See MLIR's [FunctionType](https://mlir.llvm.org/docs/Dialects/Builtin/#functiontype).
///
#[def_type("builtin.function")]
#[derive(Hash, PartialEq, Eq, Debug)]
pub struct FunctionType {
    /// Function arguments / inputs.
    inputs: Vec<Ptr<TypeObj>>,
    /// Function results / outputs.
    results: Vec<Ptr<TypeObj>>,
}

impl FunctionType {
    /// Get or create a new Function type.
    pub fn get(
        ctx: &mut Context,
        inputs: Vec<Ptr<TypeObj>>,
        results: Vec<Ptr<TypeObj>>,
    ) -> TypePtr<Self> {
        Type::register_instance(FunctionType { inputs, results }, ctx)
    }
    /// Get, if it already exists, a Function type.
    pub fn get_existing(
        ctx: &Context,
        inputs: Vec<Ptr<TypeObj>>,
        results: Vec<Ptr<TypeObj>>,
    ) -> Option<TypePtr<Self>> {
        Type::get_instance(FunctionType { inputs, results }, ctx)
    }

    /// Get a reference to the function input / argument types.
    pub fn get_inputs(&self) -> &Vec<Ptr<TypeObj>> {
        &self.inputs
    }

    /// Get a reference to the function result / output types.
    pub fn get_results(&self) -> &Vec<Ptr<TypeObj>> {
        &self.results
    }
}

impl Printable for FunctionType {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        let sep = ListSeparator::Char(',');
        functional_type(
            list_with_sep(&self.inputs, sep),
            list_with_sep(&self.results, sep),
        )
        .fmt(ctx, state, f)
    }
}

impl Parsable for FunctionType {
    type Arg = ();
    type Parsed = TypePtr<Self>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        let type_list_parser = || spaced(delimited_list_parser('(', ')', ',', type_parser()));
        let mut parser = spaced(between(
            token('<'),
            token('>'),
            type_list_parser()
                .skip(spaced(string("->")))
                .and(type_list_parser()),
        ));
        parser
            .parse_stream(state_stream)
            .map(|(inputs, results)| Self::get(state_stream.state.ctx, inputs, results))
            .into()
    }
}

impl Verify for FunctionType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        todo!()
    }
}

#[def_type("builtin.unit")]
#[derive(Hash, PartialEq, Eq, Debug)]
pub struct UnitType;

impl UnitType {
    /// Get or create a new unit type.
    pub fn get(ctx: &mut Context) -> TypePtr<Self> {
        Type::register_instance(Self {}, ctx)
    }
}

impl Printable for UnitType {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        _f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        Ok(())
    }
}

impl Parsable for UnitType {
    type Arg = ();
    type Parsed = TypePtr<Self>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        Ok(UnitType::get(state_stream.state.ctx)).into_parse_result()
    }
}

impl_verify_succ!(UnitType);

pub fn register(dialect: &mut Dialect) {
    IntegerType::register_type_in_dialect(dialect, IntegerType::parser_fn);
    FunctionType::register_type_in_dialect(dialect, FunctionType::parser_fn);
    UnitType::register_type_in_dialect(dialect, UnitType::parser_fn);
}

#[cfg(test)]
mod tests {
    use combine::{eof, Parser};
    use expect_test::expect;

    use super::FunctionType;
    use crate::{
        context::Context,
        dialects::{
            self,
            builtin::types::{IntegerType, Signedness},
        },
        location,
        parsable::{self, state_stream_from_iterator, Parsable},
        r#type::Type,
    };
    #[test]
    fn test_integer_types() {
        let mut ctx = Context::new();

        let int32_1_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int32_2_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signed);
        let uint32_ptr = IntegerType::get(&mut ctx, 32, Signedness::Unsigned);

        assert!(int32_1_ptr.deref(&ctx).hash_type() == int32_2_ptr.deref(&ctx).hash_type());
        assert!(int32_1_ptr.deref(&ctx).hash_type() != int64_ptr.deref(&ctx).hash_type());
        assert!(int32_1_ptr.deref(&ctx).hash_type() != uint32_ptr.deref(&ctx).hash_type());
        assert!(int32_1_ptr == int32_2_ptr);
        assert!(int32_1_ptr != int64_ptr);
        assert!(int32_1_ptr != uint32_ptr);

        assert!(int32_1_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_1_ptr.into());
        assert!(int32_2_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_1_ptr.into());
        assert!(int32_2_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_2_ptr.into());
        assert!(int64_ptr.deref(&ctx).get_self_ptr(&ctx) == int64_ptr.into());
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) == uint32_ptr.into());
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) != int32_1_ptr.into());
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) != int64_ptr.into());
    }

    #[test]
    fn test_function_types() {
        let mut ctx = Context::new();
        let int32_1_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signed);

        let ft_ref = FunctionType::get(&mut ctx, vec![int32_1_ptr.into()], vec![int64_ptr.into()])
            .deref(&ctx);
        assert!(
            ft_ref.get_inputs()[0] == int32_1_ptr.into()
                && ft_ref.get_results()[0] == int64_ptr.into()
        );
    }

    #[test]
    fn test_integer_parsing() {
        let mut ctx = Context::new();
        let state_stream = state_stream_from_iterator(
            "<si64>".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = IntegerType::parser(())
            .and(eof())
            .parse(state_stream)
            .unwrap()
            .0
             .0;
        assert!(
            res == IntegerType::get_existing(&ctx, 64, Signedness::Signed)
                .unwrap()
                .into()
        )
    }

    #[test]
    fn test_integer_parsing_errs() {
        let mut ctx = Context::new();
        let a = "<asi64>".to_string();
        let state_stream = state_stream_from_iterator(
            a.chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = IntegerType::parser(()).parse(state_stream);
        let err_msg = format!("{}", res.err().unwrap());

        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 2
            Unexpected `a`
            Expected whitespaces, si, ui or i
        "#]];
        expected_err_msg.assert_eq(&err_msg);
    }

    #[test]
    fn test_fntype_parsing() {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);

        let si32 = IntegerType::get(&mut ctx, 32, Signedness::Signed);

        let state_stream = state_stream_from_iterator(
            "<() -> (builtin.int <si32>)>".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = FunctionType::parser(())
            .and(eof())
            .parse(state_stream)
            .unwrap()
            .0
             .0;
        assert!(
            res == FunctionType::get_existing(&ctx, vec![], vec![si32.into()])
                .unwrap()
                .into()
        )
    }
}
