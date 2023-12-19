use combine::{
    between, choice, easy, many1,
    parser::{char::digit, char::string},
    sep_by, token, ParseResult, Parser, Positioned,
};

use crate::{
    common_traits::Verify,
    context::{Context, Ptr},
    dialect::Dialect,
    error::Result,
    impl_type,
    parsable::{spaced, to_parse_result, Parsable, StateStream},
    printable::{self, ListSeparator, Printable, PrintableIter},
    r#type::{type_parser, Type, TypeObj},
    storage_uniquer::TypeValueHash,
};

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
pub enum Signedness {
    Signed,
    Unsigned,
    Signless,
}

#[derive(Hash, PartialEq, Eq)]
pub struct IntegerType {
    width: u64,
    signedness: Signedness,
}
impl_type!(IntegerType, "int", "builtin");

impl IntegerType {
    /// Get or create a new integer type.
    pub fn get(ctx: &mut Context, width: u64, signedness: Signedness) -> Ptr<TypeObj> {
        Type::register_instance(IntegerType { width, signedness }, ctx)
    }
    /// Get, if it already exists, an integer type.
    pub fn get_existing(ctx: &Context, width: u64, signedness: Signedness) -> Option<Ptr<TypeObj>> {
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
    type Parsed = Ptr<TypeObj>;
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>>
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
    }
}

impl Printable for IntegerType {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{} <", Self::get_type_id_static().disp(ctx))?;
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
#[derive(Hash, PartialEq, Eq)]
pub struct FunctionType {
    /// Function arguments / inputs.
    inputs: Vec<Ptr<TypeObj>>,
    /// Function results / outputs.
    results: Vec<Ptr<TypeObj>>,
}
impl_type!(FunctionType, "function", "builtin");

impl FunctionType {
    /// Get or create a new Function type.
    pub fn get(
        ctx: &mut Context,
        inputs: Vec<Ptr<TypeObj>>,
        results: Vec<Ptr<TypeObj>>,
    ) -> Ptr<TypeObj> {
        Type::register_instance(FunctionType { inputs, results }, ctx)
    }
    /// Get, if it already exists, a Function type.
    pub fn get_existing(
        ctx: &Context,
        inputs: Vec<Ptr<TypeObj>>,
        results: Vec<Ptr<TypeObj>>,
    ) -> Option<Ptr<TypeObj>> {
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
        write!(
            f,
            "{} <({}) -> ({})>",
            Self::get_type_id_static().disp(ctx),
            self.inputs.iter().iprint(ctx, state, sep),
            self.results.iter().iprint(ctx, state, sep)
        )
    }
}

impl Parsable for FunctionType {
    type Arg = ();
    type Parsed = Ptr<TypeObj>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>>
    where
        Self: Sized,
    {
        let type_list_parser = || {
            spaced(between(
                token('('),
                token(')'),
                sep_by::<Vec<_>, _, _, _>(spaced(type_parser()), token(',')),
            ))
        };
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
    }
}

impl Verify for FunctionType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        todo!()
    }
}

#[derive(Hash, PartialEq, Eq)]
pub struct UnitType;
impl_type!(UnitType, "unit", "builtin");

impl UnitType {
    /// Get or create a new unit type.
    pub fn get(ctx: &mut Context) -> Ptr<TypeObj> {
        Type::register_instance(UnitType, ctx)
    }
}

impl Printable for UnitType {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{}", Self::get_type_id_static().disp(ctx),)
    }
}

impl Parsable for UnitType {
    type Arg = ();
    type Parsed = Ptr<TypeObj>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>>
    where
        Self: Sized,
    {
        to_parse_result(
            Ok(UnitType::get(state_stream.state.ctx)),
            state_stream.position(),
        )
    }
}

impl Verify for UnitType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

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
        dialects::builtin::types::{IntegerType, Signedness},
        parsable::{self, state_stream_from_iterator, Parsable},
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

        assert!(int32_1_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_1_ptr);
        assert!(int32_2_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_1_ptr);
        assert!(int32_2_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_2_ptr);
        assert!(int64_ptr.deref(&ctx).get_self_ptr(&ctx) == int64_ptr);
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) == uint32_ptr);
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) != int32_1_ptr);
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) != int64_ptr);
    }

    #[test]
    fn test_function_types() {
        let mut ctx = Context::new();
        let int32_1_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signed);

        let ft = FunctionType::get(&mut ctx, vec![int32_1_ptr], vec![int64_ptr]).deref(&ctx);
        let ft_ref = ft.downcast_ref::<FunctionType>().unwrap();
        assert!(ft_ref.get_inputs()[0] == int32_1_ptr && ft_ref.get_results()[0] == int64_ptr);
    }

    #[test]
    fn test_integer_parsing() {
        let mut ctx = Context::new();
        let state_stream =
            state_stream_from_iterator("<si64>".chars(), parsable::State::new(&mut ctx));

        let res = IntegerType::parser(())
            .and(eof())
            .parse(state_stream)
            .unwrap()
            .0
             .0;
        assert!(res == IntegerType::get_existing(&ctx, 64, Signedness::Signed).unwrap())
    }

    #[test]
    fn test_integer_parsing_errs() {
        let mut ctx = Context::new();
        let a = "<asi64>".to_string();
        let state_stream = state_stream_from_iterator(a.chars(), parsable::State::new(&mut ctx));

        let res = IntegerType::parser(()).parse(state_stream);
        let err_msg = format!("{}", res.err().unwrap());

        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 2
            Unexpected `a`
            Expected whitespaces, si, ui or i
        "#]];
        expected_err_msg.assert_eq(&err_msg);
    }
}
