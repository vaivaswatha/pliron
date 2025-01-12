//! Test format derive for plain structs, attributes / types.

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
    assert_eq!("{inner=builtin.int <si64>}", &printed);

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
    assert_eq!("BubbleWrap[builtin.int <si64>]", &printed);

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

#[format]
struct DoubleWrap {
    one: TypePtr<IntegerType>,
    two: IntWrapper,
}

#[test]
fn double_wrap() {
    let ctx = &mut setup_context_dialects();
    let int_ty = IntegerType::get(ctx, 64, pliron::builtin::types::Signedness::Signed);
    let test_ty_intermediate = IntWrapper { inner: int_ty };
    let test_ty = DoubleWrap {
        one: int_ty,
        two: test_ty_intermediate,
    };

    let printed = test_ty.disp(ctx).to_string();
    assert_eq!(
        "{one=builtin.int <si64>,two={inner=builtin.int <si64>}}",
        &printed
    );

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let (res, _) = DoubleWrap::parser(())
        .parse(state_stream)
        .expect("DoubleWrap parser failed");
    assert_eq!(res.disp(ctx).to_string(), printed);
}

#[format]
enum Enum {
    A(TypePtr<IntegerType>),
    B {
        one: TypePtr<IntegerType>,
        two: IntWrapper,
    },
    C,
}

#[test]
fn enum_test() {
    let ctx = &mut setup_context_dialects();
    let int_ty = IntegerType::get(ctx, 64, pliron::builtin::types::Signedness::Signed);
    let test_ty = Enum::B {
        one: int_ty,
        two: IntWrapper { inner: int_ty },
    };

    let printed = test_ty.disp(ctx).to_string();
    assert_eq!(
        "B{one=builtin.int <si64>,two={inner=builtin.int <si64>}}",
        &printed
    );

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let (res, _) = Enum::parser(())
        .parse(state_stream)
        .expect("Enum parser failed");
    assert_eq!(res.disp(ctx).to_string(), printed);

    let test_ty = Enum::A(int_ty);
    let printed = test_ty.disp(ctx).to_string();
    assert_eq!("A(builtin.int <si64>)", &printed);

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let (res, _) = Enum::parser(())
        .parse(state_stream)
        .expect("Enum parser failed");

    assert_eq!(res.disp(ctx).to_string(), printed);

    let test_ty = Enum::C;
    let printed = test_ty.disp(ctx).to_string();
    assert_eq!("C", &printed);

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let (res, _) = Enum::parser(())
        .parse(state_stream)
        .expect("Enum parser failed");

    assert_eq!(res.disp(ctx).to_string(), printed);
}

#[format]
struct U64Wrapper {
    a: u64,
}

#[test]
fn u64_wrapper() {
    let ctx = &mut setup_context_dialects();
    let test_ty = U64Wrapper { a: 42 };

    let printed = test_ty.disp(ctx).to_string();
    assert_eq!("{a=42}", &printed);

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let (res, _) = U64Wrapper::parser(())
        .parse(state_stream)
        .expect("U64Wrapper parser failed");
    assert_eq!(res.disp(ctx).to_string(), printed);
}

#[format("$upper `/` $lower")]
struct IntDiv {
    upper: u64,
    lower: u64,
}

#[test]
fn int_div() {
    let ctx = &mut setup_context_dialects();
    let test_ty = IntDiv {
        upper: 42,
        lower: 7,
    };

    let printed = test_ty.disp(ctx).to_string();
    assert_eq!("42/7", &printed);

    let state_stream = state_stream_from_iterator(
        printed.chars(),
        parsable::State::new(ctx, location::Source::InMemory),
    );
    let (res, _) = IntDiv::parser(())
        .parse(state_stream)
        .expect("IntDiv parser failed");
    assert_eq!(res.disp(ctx).to_string(), printed);
}
