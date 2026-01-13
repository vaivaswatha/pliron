//! Attributes are non-SSA data stored in [Operation](crate::operation::Operation)s.
//!
//! See [MLIR Attributes](https://mlir.llvm.org/docs/LangRef/#attributes).
//! Unlike in MLIR, we do not unique attributes, and hence they are mutable.
//! These are similar in concept to [Properties](https://discourse.llvm.org/t/rfc-introducing-mlir-operation-properties/67846).
//! Attribute objects are boxed and not wrapped with [Ptr](crate::context::Ptr).
//! They are heavy (i.e., not just a pointer, handle or reference),
//! making clones potentially expensive.
//!
//! The [def_attribute](pliron::derive::def_attribute) proc macro from the
//! pliron-derive create can be used to implement [Attribute] for a rust type.
//!
//! Common semantics, API and behaviour of [Attribute]s are
//! abstracted into interfaces. Interfaces in pliron capture MLIR
//! functionality of both [Traits](https://mlir.llvm.org/docs/Traits/)
//! and [Interfaces](https://mlir.llvm.org/docs/Interfaces/).
//! Interfaces must all implement an associated function named `verify` with
//! the type [AttrInterfaceVerifier].
//!
//! Interfaces are rust Trait definitions annotated with the attribute macro
//! [attr_interface](pliron::derive::attr_interface). The attribute ensures that any
//! verifiers of super-interfaces are run prior to the verifier of this interface.
//! Note: Super-interface verifiers *may* run multiple times for the same attribute.
//!
//! [Attribute]s that implement an interface must annotate the implementation with
//! [attr_interface_impl](pliron::derive::attr_interface_impl) macro to ensure that
//! the interface verifier is automatically called during verification
//! and that a `&dyn Attribute` object can be [cast](attr_cast) into an interface object,
//! (or that it can be checked if the interface is [implemented](attr_impls))
//! with ease.
//!
//! Use [verify_attr] to verify an [Attribute] object.
//! This function verifies all interfaces implemented by the attribute, and then the attribute itself.
//! The attribute's verifier must explicitly invoke verifiers on any sub-objects it contains.
//!
//! [AttrObj]s can be downcasted to their concrete types using
//! [downcast_rs](https://docs.rs/downcast-rs/1.2.0/downcast_rs/index.html#example-without-generics).

use std::{
    collections::BTreeMap,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    ops::Deref,
    sync::LazyLock,
};

use combine::{Parser, parser, token};
use downcast_rs::{Downcast, impl_downcast};
use dyn_clone::DynClone;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    builtin::attr_interfaces::OutlinedAttr,
    common_traits::Verify,
    context::Context,
    dialect::DialectName,
    identifier::Identifier,
    impl_printable_for_display, input_err,
    irfmt::{
        parsers::{attr_parser, delimited_list_parser, spaced},
        printers::iter_with_sep,
    },
    location::Located,
    parsable::{Parsable, ParseResult, ParserFn, StateStream},
    printable::{self, Printable},
    result::Result,
    storage_uniquer::TypeValueHash,
};

/// Convenience type to easily print and parse key-value pairs in an [AttributeDict].
#[derive(Clone)]
struct AttributeDictKeyVal<'a> {
    key: &'a Identifier,
    val: &'a AttrObj,
}

impl<'a> Printable for AttributeDictKeyVal<'a> {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "{}: {}", self.key, self.val.disp(ctx))
    }
}

impl<'b> Parsable for AttributeDictKeyVal<'b> {
    type Arg = ();

    type Parsed = (Identifier, AttrObj);

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        (Identifier::parser(()), spaced(token(':')), attr_parser())
            .map(|(key, _, val)| (key, val))
            .parse_stream(state_stream)
            .into_result()
    }
}

impl Printable for AttributeDict {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "[{}]",
            iter_with_sep(
                self.0
                    .iter()
                    .map(|(key, val)| AttributeDictKeyVal { key, val }),
                printable::ListSeparator::CharSpace(','),
            )
            .disp(ctx)
        )
    }
}

impl Parsable for AttributeDict {
    type Arg = ();
    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        delimited_list_parser('[', ']', ',', AttributeDictKeyVal::parser(()))
            .map(|key_vals| AttributeDict(key_vals.into_iter().collect()))
            .parse_stream(state_stream)
            .into_result()
    }
}

/// A dictionary of attributes, mapping keys to attribute objects.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct AttributeDict(pub FxHashMap<Identifier, AttrObj>);

impl Hash for AttributeDict {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let self_btree: BTreeMap<_, _> = self.0.iter().collect();
        // Hash the BTreeMap to ensure that the order of keys does not affect the hash.
        self_btree.hash(state);
    }
}

impl AttributeDict {
    /// Get reference to attribute value that is mapped to key `k`.
    pub fn get<T: Attribute>(&self, k: &Identifier) -> Option<&T> {
        self.0.get(k).and_then(|ao| ao.downcast_ref::<T>())
    }

    /// Get mutable reference to attribute value that is mapped to key `k`.
    pub fn get_mut<T: Attribute>(&mut self, k: &Identifier) -> Option<&mut T> {
        self.0.get_mut(k).and_then(|ao| ao.downcast_mut::<T>())
    }

    /// Reference to the attribute value (that is mapped to key `k`) as an interface reference.
    pub fn get_as<T: ?Sized + Attribute>(&self, k: &Identifier) -> Option<&T> {
        self.0.get(k).and_then(|ao| attr_cast::<T>(&**ao))
    }

    /// Set the attribute value for key `k`.
    pub fn set<T: Attribute>(&mut self, k: Identifier, v: T) {
        self.0.insert(k, Box::new(v));
    }

    /// Clone, but skip Outlined attributes.
    pub fn clone_skip_outlined(&self) -> Self {
        self.0
            .iter()
            .filter_map(|(k, v)| {
                if attr_impls::<dyn OutlinedAttr>(&**v) {
                    None
                } else {
                    Some((k.clone(), dyn_clone::clone_box(&**v)))
                }
            })
            .collect::<FxHashMap<Identifier, AttrObj>>()
            .into()
    }
}

impl From<FxHashMap<Identifier, AttrObj>> for AttributeDict {
    fn from(value: FxHashMap<Identifier, AttrObj>) -> Self {
        AttributeDict(value)
    }
}

/// Basic functionality that every attribute in the IR must implement.
///
/// See [module](crate::attribute) documentation for more information.
pub trait Attribute: Printable + Verify + Downcast + Sync + Send + DynClone + Debug {
    /// Compute and get the hash for this instance of Self.
    /// Hash collisions can be a possibility.
    fn hash_attr(&self) -> TypeValueHash;

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
    fn register_attr_in_dialect<A: Attribute>(ctx: &mut Context, attr_parser: ParserFn<(), A>)
    where
        Self: Sized,
    {
        // Specifying higher ranked lifetime on a closure:
        // https://stackoverflow.com/a/46198877/2128804
        fn constrain<F>(f: F) -> F
        where
            F: for<'a> Fn(
                &'a (),
            ) -> Box<
                dyn Parser<StateStream<'a>, Output = AttrObj, PartialState = ()> + 'a,
            >,
        {
            f
        }
        let attr_parser = constrain(move |_| {
            combine::parser(move |parsable_state: &mut StateStream<'_>| {
                attr_parser(&(), ())
                    .parse_stream(parsable_state)
                    .map(|attr| -> AttrObj { Box::new(attr) })
                    .into_result()
            })
            .boxed()
        });
        let attrid = Self::get_attr_id_static();
        let dialect = ctx
            .dialects
            .get_mut(&attrid.dialect)
            .unwrap_or_else(|| panic!("Unregistered dialect {}", &attrid.dialect));
        dialect.add_attr(Self::get_attr_id_static(), Box::new(attr_parser));
    }
}
impl_downcast!(Attribute);
dyn_clone::clone_trait_object!(Attribute);

/// [Attribute] objects are boxed and stored in the IR.
pub type AttrObj = Box<dyn Attribute>;

/// A storable closure for parsing any [AttrId] followed by the full [Attribute].
pub(crate) type AttrParserFn = Box<
    dyn for<'a> Fn(
        &'a (),
    )
        -> Box<dyn Parser<StateStream<'a>, Output = AttrObj, PartialState = ()> + 'a>,
>;

impl PartialEq for AttrObj {
    fn eq(&self, other: &Self) -> bool {
        (**self).eq_attr(&**other)
    }
}

impl<T: Attribute> From<T> for AttrObj {
    fn from(value: T) -> Self {
        Box::new(value)
    }
}

impl Eq for AttrObj {}

impl Hash for AttrObj {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write(&u64::from(self.hash_attr()).to_ne_bytes())
    }
}

impl Printable for AttrObj {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{} ", self.get_attr_id())?;
        Printable::fmt(self.deref(), ctx, state, f)
    }
}

impl Parsable for AttrObj {
    type Arg = ();
    type Parsed = AttrObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        let loc = state_stream.loc();
        let attr_id_parser = spaced(AttrId::parser(()));

        let mut attr_parser = attr_id_parser.then(move |attr_id: AttrId| {
            let loc = loc.clone();
            combine::parser(move |parsable_state: &mut StateStream<'a>| {
                let state = &parsable_state.state;
                let dialect = state
                    .ctx
                    .dialects
                    .get(&attr_id.dialect)
                    .expect("Dialect name parsed but dialect isn't registered");
                let Some(attr_parser) = dialect.attributes.get(&attr_id) else {
                    input_err!(
                        loc.clone(),
                        "Unregistered attribute {}",
                        attr_id.disp(state.ctx)
                    )?
                };
                attr_parser(&()).parse_stream(parsable_state).into_result()
            })
        });

        attr_parser.parse_stream(state_stream).into_result()
    }
}

/// Verify an [Attribute] object.
/// 1. Verify all interfaces implemented by this attribute.
/// 2. Verify the attribute itself.
pub fn verify_attr(attr: &dyn Attribute, ctx: &Context) -> Result<()> {
    // Verify all interfaces implemented by this attribute.
    attr.verify_interfaces(ctx)?;

    // Verify the attribute itself.
    Verify::verify(attr, ctx)
}

impl Verify for AttrObj {
    fn verify(&self, ctx: &Context) -> Result<()> {
        verify_attr(self.as_ref(), ctx)
    }
}

/// Cast reference to an [Attribute] object to an interface reference.
pub fn attr_cast<T: ?Sized + Attribute>(attr: &dyn Attribute) -> Option<&T> {
    crate::utils::trait_cast::any_to_trait::<T>(attr.as_any())
}

/// Does this [Attribute] object implement interface T?
pub fn attr_impls<T: ?Sized + Attribute>(attr: &dyn Attribute) -> bool {
    attr_cast::<T>(attr).is_some()
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

impl_printable_for_display!(AttrName);

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
    ) -> ParseResult<'a, Self::Parsed>
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

impl_printable_for_display!(AttrId);

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
    ) -> ParseResult<'a, Self::Parsed>
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

/// Every attribute interface must have a function named `verify` with this type.
pub type AttrInterfaceVerifier = fn(&dyn Attribute, &Context) -> Result<()>;
/// Function returns the list of super verifiers, followed by a self verifier, for an interface.
pub type AttrInterfaceAllVerifiers = fn() -> Vec<AttrInterfaceVerifier>;

#[doc(hidden)]
/// An [Attribute] paired with an interface it implements
/// (specifically the verifiers (including super verifiers) for that interface).
type AttrInterfaceVerifierInfo = (AttrId, AttrInterfaceAllVerifiers);

#[cfg(not(target_family = "wasm"))]
pub mod statics {
    use super::*;

    #[::pliron::linkme::distributed_slice]
    pub static ATTR_INTERFACE_VERIFIERS: [LazyLock<AttrInterfaceVerifierInfo>] = [..];

    pub fn get_attr_interface_verifiers()
    -> impl Iterator<Item = &'static LazyLock<AttrInterfaceVerifierInfo>> {
        ATTR_INTERFACE_VERIFIERS.iter()
    }
}

#[cfg(target_family = "wasm")]
pub mod statics {
    use super::*;
    use crate::utils::inventory::LazyLockWrapper;

    ::pliron::inventory::collect!(LazyLockWrapper<AttrInterfaceVerifierInfo>);

    pub fn get_attr_interface_verifiers()
    -> impl Iterator<Item = &'static LazyLock<AttrInterfaceVerifierInfo>> {
        ::pliron::inventory::iter::<LazyLockWrapper<AttrInterfaceVerifierInfo>>().map(|llw| llw.0)
    }
}

pub use statics::*;

#[doc(hidden)]
/// A map from every [Attribute] to its ordered (as per interface deps) list of interface verifiers.
/// An interface's super-interfaces are to be verified before it itself is.
pub static ATTR_INTERFACE_VERIFIERS_MAP: LazyLock<FxHashMap<AttrId, Vec<AttrInterfaceVerifier>>> =
    LazyLock::new(|| {
        // Collect ATTR_INTERFACE_VERIFIERS into an [AttrId] indexed map.
        let mut attr_intr_verifiers = FxHashMap::default();
        for lazy in get_attr_interface_verifiers() {
            let (attr_id, all_verifiers_for_interface) = (**lazy).clone();
            attr_intr_verifiers
                .entry(attr_id)
                .and_modify(|verifiers: &mut Vec<AttrInterfaceAllVerifiers>| {
                    verifiers.push(all_verifiers_for_interface)
                })
                .or_insert(vec![all_verifiers_for_interface]);
        }

        // Remove duplicates (best effort as rustc may inline functions, resulting in different pointers).
        // Relies on `__all_verifiers` returning the super-verifiers followed by self verifier
        // to ensure that super-interfaces are verified first.
        attr_intr_verifiers
            .into_iter()
            .map(|(attr_id, verifiers)| {
                let mut dedupd_verifiers = Vec::new();
                let mut seen = FxHashSet::default();
                for verifier_fn_list in verifiers {
                    for verifier in verifier_fn_list() {
                        if seen.insert(verifier) {
                            dedupd_verifiers.push(verifier);
                        }
                    }
                }
                (attr_id, dedupd_verifiers)
            })
            .collect()
    });
