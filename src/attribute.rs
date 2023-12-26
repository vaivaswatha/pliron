//! Attributes are non-SSA data stored in [Operation](crate::operation::Operation)s.
//!
//! See [MLIR Attributes](https://mlir.llvm.org/docs/LangRef/#attributes).
//! Unlike in MLIR, we do not unique attributes, and hence they are mutable.
//! These are similar in concept to [Properties](https://discourse.llvm.org/t/rfc-introducing-mlir-operation-properties/67846).
//! Attribute objects are heavy, boxed, and not wrapped with [Ptr](crate::context::Ptr).
//! They may or may not be clonable. See [clone].
//!
//! The [impl_attr](crate::impl_attr) macro can be used to implement [Attribute] for a rust type.
//!
//! Common semantics, API and behaviour of [Attribute]s are
//! abstracted into interfaces. Interfaces in pliron capture MLIR
//! functionality of both [Traits](https://mlir.llvm.org/docs/Traits/)
//! and [Interfaces](https://mlir.llvm.org/docs/Interfaces/).
//! Interfaces must all implement an associated function named `verify` with
//! the type [AttrInterfaceVerifier].
//!
//! [Attribute]s that implement an interface must do so using the
//! [impl_attr_interface](crate::impl_attr_interface) macro.
//! This ensures that the interface verifier is automatically called,
//! and that a `&dyn Attribute` object can be [cast](attr_cast) into an
//! interface object, (or that it can be checked if the interface
//! is [implemented](attr_impls)) with ease.
//!
//! [AttrObj]s can be downcasted to their concrete types using
/// [downcast_rs](https://docs.rs/downcast-rs/1.2.0/downcast_rs/index.html#example-without-generics).
use std::{fmt::Display, hash::Hash, ops::Deref};

use combine::{easy, error::StdParseResult2, parser, ParseResult, Parser, Positioned, StreamOnce};
use downcast_rs::{impl_downcast, Downcast};
use intertrait::{cast::CastRef, CastFrom};

use crate::{
    common_traits::Verify,
    context::Context,
    dialect::{Dialect, DialectName},
    error::Result,
    identifier::Identifier,
    input_err,
    parsable::{spaced, IntoStdParseResult2, Parsable, ParserFn, StateStream},
    printable::{self, Printable},
};

/// Basic functionality that every attribute in the IR must implement.
///
/// See [module](crate::attribute) documentation for more information.
pub trait Attribute: Printable + Verify + Downcast + CastFrom + Sync {
    /// Is self equal to an other Attribute?
    fn eq_attr(&self, other: &dyn Attribute) -> bool;

    /// Get an [Attribute]'s static name. This is *not* per instantnce.
    /// It is mostly useful for printing and parsing the attribute.
    fn get_attr_id(&self) -> AttrId;

    /// Same as [get_attr_id](Self::get_attr_id), but without the self reference.
    fn get_attr_id_static() -> AttrId
    where
        Self: Sized;

    /// Verify all interfaces implemented by this attribute.
    fn verify_interfaces(&self, ctx: &Context) -> Result<()>;

    /// Register this attribute's [AttrId] in the dialect it belongs to.
    /// **Warning**: No check is made as to whether this attr is already registered
    ///  in `dialect`.
    fn register_attr_in_dialect(dialect: &mut Dialect, attr_parser: ParserFn<(), AttrObj>)
    where
        Self: Sized,
    {
        dialect.add_attr(Self::get_attr_id_static(), attr_parser);
    }
}
impl_downcast!(Attribute);

/// [Attribute] objects are boxed and stored in the IR.
pub type AttrObj = Box<dyn Attribute>;

impl PartialEq for AttrObj {
    fn eq(&self, other: &Self) -> bool {
        (**self).eq_attr(&**other)
    }
}

impl Eq for AttrObj {}

/// Clone clonable attributes.
/// ```
///     # use pliron::{attribute, dialects::builtin::
///     #    {types::{IntegerType, Signedness}, attributes::IntegerAttr}, context::Context};
///     # use apint::ApInt;
///     # let mut ctx = Context::new();
///     let i64_ty = IntegerType::get(&mut ctx, 32, Signedness::Signed);
///     let int64 = IntegerAttr::create(i64_ty, ApInt::from_i64(0));
///     let int64_clone = attribute::clone::<IntegerAttr>(&int64);
///     assert!(int64 == int64_clone);
/// ```
pub fn clone<T: Clone + Attribute>(source: &AttrObj) -> AttrObj {
    Box::new(source.downcast_ref::<T>().unwrap().clone())
}

impl Printable for AttrObj {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        self.as_ref().fmt(ctx, state, f)
    }
}

/// Cast reference to an [Attribute] object to an interface reference.
pub fn attr_cast<T: ?Sized + Attribute>(attr: &dyn Attribute) -> Option<&T> {
    attr.cast::<T>()
}

/// Does this [Attribute] object implement interface T?
pub fn attr_impls<T: ?Sized + Attribute>(attr: &dyn Attribute) -> bool {
    attr.impls::<T>()
}

#[derive(Clone, Hash, PartialEq, Eq)]
/// An [Attribute]'s name (not including it's dialect).
pub struct AttrName(String);

impl AttrName {
    /// Create a new AttrName.
    pub fn new(name: &str) -> AttrName {
        AttrName(name.to_string())
    }
}

impl Printable for AttrName {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl Display for AttrName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Parsable for AttrName {
    type Arg = ();
    type Parsed = AttrName;

    fn parse<'a>(
        state_stream: &mut crate::parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> StdParseResult2<Self::Parsed, <StateStream<'a> as StreamOnce>::Error>
    where
        Self: Sized,
    {
        Identifier::parser(())
            .map(|name| AttrName::new(&name))
            .parse_stream(state_stream)
            .into()
    }
}

impl Deref for AttrName {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
/// A combination of a Attr's name and its dialect.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct AttrId {
    pub dialect: DialectName,
    pub name: AttrName,
}

impl Printable for AttrId {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl Display for AttrId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.dialect, self.name)
    }
}

impl Parsable for AttrId {
    type Arg = ();
    type Parsed = AttrId;

    // Parses (but does not validate) a TypeId.
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> StdParseResult2<Self::Parsed, <StateStream<'a> as StreamOnce>::Error>
    where
        Self: Sized,
    {
        let mut parser = DialectName::parser(())
            .skip(parser::char::char('.'))
            .and(AttrName::parser(()))
            .map(|(dialect, name)| AttrId { dialect, name });
        parser.parse_stream(state_stream).into()
    }
}

/// Parse an identified attribute, which is [AttrId] followed by its contents.
pub fn attr_parse<'a>(
    state_stream: &mut StateStream<'a>,
) -> ParseResult<AttrObj, easy::ParseError<StateStream<'a>>> {
    let position = state_stream.stream.position();
    let attr_id_parser = spaced(AttrId::parser(()));

    let mut attr_parser = attr_id_parser.then(|attr_id: AttrId| {
        combine::parser(move |parsable_state: &mut StateStream<'a>| {
            let state = &parsable_state.state;
            let dialect = state
                .ctx
                .dialects
                .get(&attr_id.dialect)
                .expect("Dialect name parsed but dialect isn't registered");
            let Some(attr_parser) = dialect.attributes.get(&attr_id) else {
                return input_err!("Unregistered attribute {}", attr_id.disp(state.ctx))
                    .into_pres2(position);
            };
            attr_parser(&(), ())
                .parse_stream(parsable_state)
                .into_result()
        })
    });

    attr_parser.parse_stream(state_stream)
}

/// A parser combinator to parse [AttrId] followed by the attribute's contents.
pub fn attr_parser<'a>(
) -> Box<dyn Parser<StateStream<'a>, Output = AttrObj, PartialState = ()> + 'a> {
    combine::parser(|parsable_state: &mut StateStream<'a>| attr_parse(parsable_state).into_result())
        .boxed()
}

/// Every attribute interface must have a function named `verify` with this type.
pub type AttrInterfaceVerifier = fn(&dyn Attribute, &Context) -> Result<()>;

/// impl [Attribute] for a rust type.
///
/// Usage:
/// ```
/// #[derive(PartialEq, Eq)]
/// struct MyAttr { }
/// impl_attr!(
///     /// MyAttr is mine
///     MyAttr,
///     "name",
///     "dialect"
/// );
/// # use pliron::{
/// #     impl_attr, printable::{self, Printable},
/// #     context::Context, error::Result, common_traits::Verify,
/// #     attribute::Attribute,
/// # };
/// # impl Printable for MyAttr {
/// #    fn fmt(&self,
/// #           _ctx: &Context,
/// #           _state: &printable::State,
/// #           _f: &mut core::fmt::Formatter<'_>)
/// #        -> core::fmt::Result
/// #    {
/// #        todo!()
/// #    }
/// # }
///
/// # impl Verify for MyAttr {
/// #   fn verify(&self, _ctx: &Context) -> Result<()> {
/// #        todo!()
/// #    }
/// # }
/// ```
/// **Note**: pre-requisite traits for [Attribute] must already be implemented.
///         Additionaly, PartialEq must be implemented by the type.
#[macro_export]
macro_rules! impl_attr {
    (   $(#[$outer:meta])*
        $structname: ident, $attr_name: literal, $dialect_name: literal) => {
        paste::paste!{
            #[allow(non_camel_case_types)]
            pub struct [<AttrInterfaceVerifier_ $structname>](pub $crate::attribute::AttrInterfaceVerifier);
            impl $structname {
                pub const fn build_interface_verifier(verifier: $crate::attribute::AttrInterfaceVerifier) ->
                [<AttrInterfaceVerifier_ $structname>] {
                    [<AttrInterfaceVerifier_ $structname>](verifier)
                }
            }
            inventory::collect!([<AttrInterfaceVerifier_ $structname>]);
        }
        $(#[$outer])*
        impl $crate::attribute::Attribute for $structname {
            fn eq_attr(&self, other: &dyn Attribute) -> bool {
                other
                    .downcast_ref::<Self>()
                    .map_or(false, |other| other == self)
            }

            fn get_attr_id(&self) -> $crate::attribute::AttrId {
                Self::get_attr_id_static()
            }

            fn get_attr_id_static() -> $crate::attribute::AttrId {
                $crate::attribute::AttrId {
                    name: $crate::attribute::AttrName::new($attr_name),
                    dialect: $crate::dialect::DialectName::new($dialect_name),
                }
            }
            fn verify_interfaces(&self, ctx: &Context) -> $crate::error::Result<()> {
                let interface_verifiers = paste::paste!{
                    inventory::iter::<[<AttrInterfaceVerifier_ $structname>]>
                };
                for verifier in interface_verifiers {
                    (verifier.0)(self, ctx)?;
                }
                Ok(())
            }
        }
    }
}

/// Implement an Attribute Interface for an Attribute.
/// The interface trait must define a `verify` function with type [AttrInterfaceVerifier].
///
/// Usage:
/// ```
/// #[derive(PartialEq, Eq)]
/// struct MyAttr { }
/// impl_attr!(
///     /// MyAttr is mine
///     MyAttr,
///     "name",
///     "dialect"
/// );
/// trait MyAttrInterface: Attribute {
///     fn monu(&self);
///     fn verify(attr: &dyn Attribute, ctx: &Context) -> Result<()>
///         where
///         Self: Sized,
///     {
///         Ok(())
///     }
/// }
/// impl_attr_interface!(
///     MyAttrInterface for MyAttr
///     {
///         fn monu(&self) { println!("monu"); }
///     }
/// );
/// # use pliron::{
/// #     impl_attr, printable::{self, Printable},
/// #     context::Context, error::Result, common_traits::Verify,
/// #     attribute::Attribute, impl_attr_interface
/// # };
/// # impl Printable for MyAttr {
/// #    fn fmt(&self, _ctx: &Context, _state: &printable::State, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
/// #        todo!()
/// #    }
/// # }
///
/// # impl Verify for MyAttr {
/// #   fn verify(&self, _ctx: &Context) -> Result<()> {
/// #        todo!()
/// #    }
/// # }
#[macro_export]
macro_rules! impl_attr_interface {
    ($intr_name:ident for $attr_name:path { $($tt:tt)* }) => {
        paste::paste!{
            inventory::submit! {
                $attr_name::build_interface_verifier(<$attr_name as $intr_name>::verify)
            }
        }

        #[intertrait::cast_to]
        impl $intr_name for $attr_name {
            $($tt)*
        }
    };
}
