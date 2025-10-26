use combine::{
    Parser, choice,
    parser::char::{spaces, string},
};
use pliron::derive::def_type;
use pliron_derive::{format_type, type_interface_impl};

use crate::{
    builtin::type_interfaces::{FloatTypeInterface, FunctionTypeInterface},
    context::{Context, Ptr},
    impl_verify_succ,
    irfmt::parsers::int_parser,
    parsable::{Parsable, ParseResult, StateStream},
    printable::{self, Printable},
    r#type::{Type, TypeObj, TypePtr},
    utils::apfloat::{self, GetSemantics, Semantics},
};

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Signedness {
    Signed,
    Unsigned,
    Signless,
}

#[def_type("builtin.integer")]
#[derive(Hash, PartialEq, Eq, Debug, Clone)]
pub struct IntegerType {
    width: u32,
    signedness: Signedness,
}

impl IntegerType {
    /// Get or create a new integer type.
    pub fn get(ctx: &mut Context, width: u32, signedness: Signedness) -> TypePtr<Self> {
        Type::register_instance(IntegerType { width, signedness }, ctx)
    }
    /// Get, if it already exists, an integer type.
    pub fn get_existing(
        ctx: &Context,
        width: u32,
        signedness: Signedness,
    ) -> Option<TypePtr<Self>> {
        Type::get_instance(IntegerType { width, signedness }, ctx)
    }

    /// Get width.
    pub fn get_width(&self) -> u32 {
        self.width
    }

    /// Get signedness.
    pub fn get_signedness(&self) -> Signedness {
        self.signedness
    }

    /// Is Signed?
    pub fn is_signed(&self) -> bool {
        matches!(self.signedness, Signedness::Signed)
    }

    /// Is Unsigned?
    pub fn is_unsigned(&self) -> bool {
        matches!(self.signedness, Signedness::Unsigned)
    }

    /// Is Signless?
    pub fn is_signless(&self) -> bool {
        matches!(self.signedness, Signedness::Signless)
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
        let mut parser = spaces().with(choicer.and(int_parser()));
        parser
            .parse_stream(state_stream)
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
        match &self.signedness {
            Signedness::Signed => write!(f, "si{}", self.width)?,
            Signedness::Unsigned => write!(f, "ui{}", self.width)?,
            Signedness::Signless => write!(f, "i{}", self.width)?,
        };
        Ok(())
    }
}

impl_verify_succ!(IntegerType);

/// Map from a list of inputs to a list of results
///
/// See MLIR's [FunctionType](https://mlir.llvm.org/docs/Dialects/Builtin/#functiontype).
///
#[def_type("builtin.function")]
#[derive(Hash, PartialEq, Eq, Debug)]
#[format_type(
    "`<` `(` vec($inputs, CharSpace(`,`)) `)` `->` `(`vec($results, CharSpace(`,`)) `)` `>`"
)]
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
}

#[type_interface_impl]
impl FunctionTypeInterface for FunctionType {
    /// Get a reference to the function input / argument types.
    fn arg_types(&self) -> Vec<Ptr<TypeObj>> {
        self.inputs.clone()
    }

    /// Get a reference to the function result / output types.
    fn res_types(&self) -> Vec<Ptr<TypeObj>> {
        self.results.clone()
    }
}

impl_verify_succ!(FunctionType);

#[def_type("builtin.unit")]
#[format_type]
#[derive(Hash, PartialEq, Eq, Debug)]
pub struct UnitType;

impl UnitType {
    /// Get or create a new unit type.
    pub fn get(ctx: &mut Context) -> TypePtr<Self> {
        Type::register_instance(Self {}, ctx)
    }
}

impl_verify_succ!(UnitType);

#[def_type("builtin.fp32")]
#[format_type]
#[derive(Hash, PartialEq, Eq, Debug)]
pub struct FP32Type;
impl_verify_succ!(FP32Type);
#[type_interface_impl]
impl FloatTypeInterface for FP32Type {
    fn get_semantics(&self) -> Semantics {
        apfloat::Single::get_semantics()
    }
}

impl FP32Type {
    /// Register type in dialect and instantiate the singleton instance.
    pub fn register_and_instantiate(ctx: &mut Context) {
        Self::register_type_in_dialect(ctx, Self::parser_fn);
        Type::register_instance(Self {}, ctx);
    }

    /// Get the singleton fp32 type.
    pub fn get(ctx: &Context) -> TypePtr<Self> {
        Type::get_instance(Self {}, ctx).expect("FP32Type singleton not instantiated")
    }
}

#[def_type("builtin.fp64")]
#[format_type]
#[derive(Hash, PartialEq, Eq, Debug)]
pub struct FP64Type;
impl_verify_succ!(FP64Type);
#[type_interface_impl]
impl FloatTypeInterface for FP64Type {
    fn get_semantics(&self) -> Semantics {
        apfloat::Double::get_semantics()
    }
}

impl FP64Type {
    /// Register type in dialect and instantiate the singleton instance.
    pub fn register_and_instantiate(ctx: &mut Context) {
        Self::register_type_in_dialect(ctx, Self::parser_fn);
        Type::register_instance(Self {}, ctx);
    }

    /// Get or create a new fp64 type.
    pub fn get(ctx: &Context) -> TypePtr<Self> {
        Type::get_instance(Self {}, ctx).expect("FP64Type singleton not instantiated")
    }
}

pub fn register(ctx: &mut Context) {
    IntegerType::register_type_in_dialect(ctx, IntegerType::parser_fn);
    FunctionType::register_type_in_dialect(ctx, FunctionType::parser_fn);
    UnitType::register_type_in_dialect(ctx, UnitType::parser_fn);

    FP32Type::register_and_instantiate(ctx);
    FP64Type::register_and_instantiate(ctx);
}

#[cfg(test)]
mod tests {
    use combine::{Parser, eof};
    use expect_test::expect;

    use super::FunctionType;
    use crate::{
        builtin::{
            self,
            type_interfaces::FunctionTypeInterface as _,
            types::{IntegerType, Signedness},
        },
        context::Context,
        location,
        parsable::{self, Parsable, state_stream_from_iterator},
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
            ft_ref.arg_types()[0] == int32_1_ptr.into()
                && ft_ref.res_types()[0] == int64_ptr.into()
        );
    }

    #[test]
    fn test_integer_parsing() {
        let mut ctx = Context::new();
        let state_stream = state_stream_from_iterator(
            "si64".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

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
        let a = "asi64".to_string();
        let state_stream = state_stream_from_iterator(
            a.chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = IntegerType::parser(()).parse(state_stream);
        let err_msg = format!("{}", res.err().unwrap());

        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 1
            Unexpected `a`
            Expected whitespaces, si, ui or i
        "#]];
        expected_err_msg.assert_eq(&err_msg);
    }

    #[test]
    fn test_fntype_parsing() {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);

        let si32 = IntegerType::get(&mut ctx, 32, Signedness::Signed);

        let state_stream = state_stream_from_iterator(
            "<() -> (builtin.integer si32)>".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = FunctionType::parser(())
            .and(eof())
            .parse(state_stream)
            .unwrap()
            .0
            .0;
        assert!(res == FunctionType::get_existing(&ctx, vec![], vec![si32.into()]).unwrap())
    }
}
