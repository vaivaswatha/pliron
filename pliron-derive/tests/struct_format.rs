//! Test format derive for struct attributes / types.

use pliron::{
    builtin::types::IntegerType,
    location,
    parsable::{self, state_stream_from_iterator, Parsable},
    printable::Printable,
    r#type::TypePtr,
};
use pliron_derive::format;

mod common;
use common::setup_context_dialects;

#[format]
struct IntWrapper {
    inner: TypePtr<IntegerType>,
}

#[test]
fn int_wrapper() {
    let ctx = &mut setup_context_dialects();
    let int_ty = IntegerType::get(ctx, 64, pliron::builtin::types::Signedness::Signed);
    let test_ty = IntWrapper { inner: int_ty };

    let printed = test_ty.disp(ctx).to_string();
    assert_eq!("<inner=builtin.int<si64>>", &printed);

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let (res, _) = IntWrapper::parser(())
        .parse(state_stream)
        .expect("IntWrapper parser failed");
    assert_eq!(res.disp(ctx).to_string(), printed);
}

#[format("`BubbleWrap` `[` $inner `]`")]
struct IntWrapperCustom {
    inner: TypePtr<IntegerType>,
}

#[test]
fn int_wrapper_custom() {
    let ctx = &mut setup_context_dialects();
    let int_ty = IntegerType::get(ctx, 64, pliron::builtin::types::Signedness::Signed);
    let test_ty = IntWrapperCustom { inner: int_ty };

    let printed = test_ty.disp(ctx).to_string();
    assert_eq!("BubbleWrap[builtin.int<si64>]", &printed);

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let (res, _) = match IntWrapperCustom::parser(()).parse(state_stream) {
        Err(err) => panic!("IntWrapper parser failed: {}", err),
        Ok(res) => res,
    };
    assert_eq!(res.disp(ctx).to_string(), printed);
}
