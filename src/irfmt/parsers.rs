use crate::{
    attribute::AttrObj,
    basic_block::BasicBlock,
    context::Ptr,
    debug_info::set_operation_result_name,
    error::Result,
    identifier::Identifier,
    location::Location,
    operation::Operation,
    parsable::{Parsable, ParseResult, StateStream},
    r#type::TypeObj,
    use_def_lists::Value,
};
use combine::{parser::char::spaces, token, Parser, Stream};

/// Parse from `parser`, ignoring whitespace(s) before and after.
/// > **Warning**: Do not use this inside inside repeating combiners, such as [combine::many].
///     After successfully parsing one instance, if spaces are consumed to parse
///     the next one, but the next one doesn't exist, it is treated as a failure
///     that consumed some input. This messes things up. So spaces must be consumed
///     after a successfull parse, and not prior to an upcoming one.
///     A possibly right way to, for example, parse a comma separated list of [Identifier]s:
///
///```
///     # use combine::{parser::char::spaces, Parser};
///     # use pliron::parsable::Parsable;
///     let ids = spaces().with
///               (combine::sep_by::<Vec<_>, _, _, _>
///                 (pliron::identifier::Identifier::parser(()).skip(spaces()),
///                 combine::token(',').skip(spaces())));
///```
pub fn spaced<Input: Stream<Token = char>, Output>(
    parser: impl Parser<Input, Output = Output>,
) -> impl Parser<Input, Output = Output> {
    combine::between(spaces(), spaces(), parser)
}

/// A parser combinator to parse [TypeId](crate::type::TypeId) followed by the type's contents.
pub fn type_parser<'a>(
) -> Box<dyn Parser<StateStream<'a>, Output = Ptr<TypeObj>, PartialState = ()> + 'a> {
    <Ptr<TypeObj> as Parsable>::parser(())
}

/// A parser combinator to parse [AttrId](crate::attribute::AttrId) followed by the attribute's contents.
pub fn attr_parser<'a>(
) -> Box<dyn Parser<StateStream<'a>, Output = AttrObj, PartialState = ()> + 'a> {
    AttrObj::parser(())
}

/// Parse an identifier into an SSA [Value]. Typically called to parse
/// the SSA operands of an [Operation]. If the SSA value hasn't been defined yet,
/// a [forward reference](crate::dialects::builtin::ops::ForwardRefOp) is returned.
pub fn ssa_opd_parse<'a>(state_stream: &mut StateStream<'a>, _arg: ()) -> ParseResult<'a, Value> {
    Identifier::parser(())
        .parse_stream(state_stream)
        .map(|opd| {
            state_stream
                .state
                .name_tracker
                .ssa_use(state_stream.state.ctx, &opd)
        })
        .into()
}

/// A parser to parse an identifier into an SSA [Value]. Typically called to parse
/// the SSA operands of an [Operation]. If the SSA value hasn't been defined yet,
/// a [forward reference](crate::dialects::builtin::ops::ForwardRefOp) is returned.
pub fn ssa_opd_parser<'a>(
) -> Box<dyn Parser<StateStream<'a>, Output = Value, PartialState = ()> + 'a> {
    combine::parser(move |parsable_state: &mut StateStream<'a>| ssa_opd_parse(parsable_state, ()))
        .boxed()
}

/// Parse a block label into a [`Ptr<BasicBlock>`]. Typically called to parse
/// the block operands of an [Operation]. If the block doesn't exist, it's created,
pub fn block_opd_parse<'a>(
    state_stream: &mut StateStream<'a>,
    _arg: (),
) -> ParseResult<'a, Ptr<BasicBlock>> {
    token('^')
        .with(Identifier::parser(()))
        .parse_stream(state_stream)
        .map(|opd| {
            state_stream
                .state
                .name_tracker
                .block_use(state_stream.state.ctx, &opd)
        })
        .into()
}

/// Parse a block label into a [`Ptr<BasicBlock>`]. Typically called to parse
/// the block operands of an [Operation]. If the block doesn't exist, it's created,
pub fn block_opd_parser<'a>(
) -> Box<dyn Parser<StateStream<'a>, Output = Ptr<BasicBlock>, PartialState = ()> + 'a> {
    combine::parser(move |parsable_state: &mut StateStream<'a>| block_opd_parse(parsable_state, ()))
        .boxed()
}

/// After an [Operation] is fully parsed, for each result,
/// set its name and register it as an SSA definition.
pub fn process_parsed_ssa_defs(
    state_stream: &mut StateStream,
    results: &Vec<(Identifier, Location)>,
    op: Ptr<Operation>,
) -> Result<()> {
    let ctx = &mut state_stream.state.ctx;
    assert!(
        results.len() == op.deref(ctx).get_num_results(),
        "Error processing parsed SSA definitions. Result count mismatch"
    );

    let name_tracker = &mut state_stream.state.name_tracker;
    for (idx, name_loc) in results.iter().enumerate() {
        let res = op.deref(ctx).get_result(idx).unwrap();
        name_tracker.ssa_def(ctx, name_loc, res)?;
        set_operation_result_name(ctx, op, idx, name_loc.0.to_string());
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;

    use expect_test::expect;

    use crate::{
        context::Context,
        dialects, location,
        parsable::{self, state_stream_from_iterator},
        printable::Printable,
    };

    #[test]
    fn test_parse_type() {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);

        let state_stream = state_stream_from_iterator(
            "builtin.some".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = type_parser().parse(state_stream);
        let err_msg = format!("{}", res.err().unwrap());

        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 1
            Unregistered type builtin.some
        "#]];
        expected_err_msg.assert_eq(&err_msg);

        let state_stream = state_stream_from_iterator(
            "builtin.int a".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = type_parser().parse(state_stream);
        let err_msg = format!("{}", res.err().unwrap());

        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 13
            Unexpected `a`
            Expected `<`
        "#]];
        expected_err_msg.assert_eq(&err_msg);

        let state_stream = state_stream_from_iterator(
            "builtin.int <si32>".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let parsed = type_parser().parse(state_stream).unwrap().0;
        assert_eq!(parsed.disp(&ctx).to_string(), "builtin.int<si32>");
    }
}
