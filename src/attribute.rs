//! Attributes are non-SSA data stored in [Operation](crate::operation::Operation)s.
//!
//! See [MLIR Attributes](https://mlir.llvm.org/docs/LangRef/#attributes).
//! Unlike in MLIR, we do not unique attributes, and hence they are mutable.
//! These are similar in concept to [Properties](https://discourse.llvm.org/t/rfc-introducing-mlir-operation-properties/67846).
//! Attribute objects are boxed and not wrapped with [Ptr](crate::context::Ptr).
//! They are heavy (i.e., not just a pointer, handle or reference),
//! making clones potentially expensive.
//!
//! The [def_attribute](pliron_derive::def_attribute) proc macro from the
//! pliron-derive create can be used to implement [Attribute] for a rust type.
//!
//! Common semantics, API and behaviour of [Attribute]s are
//! abstracted into interfaces. Interfaces in pliron capture MLIR
//! functionality of both [Traits](https://mlir.llvm.org/docs/Traits/)
//! and [Interfaces](https://mlir.llvm.org/docs/Interfaces/).
//! Interfaces must all implement an associated function named `verify` with
//! the type [AttrInterfaceVerifier].
//! New interfaces must be specified via [decl_attr_interface](pliron::decl_attr_interface)
//! for proper verification.
//!
//! [Attribute]s that implement an interface must do so using the
//! [impl_attr_interface](crate::impl_attr_interface) macro.
//! This ensures that the interface verifier is automatically called,
//! and that a `&dyn Attribute` object can be [cast](attr_cast) into an
//! interface object, (or that it can be checked if the interface
//! is [implemented](attr_impls)) with ease.
//!
//! [AttrObj]s can be downcasted to their concrete types using
//! [downcast_rs](https://docs.rs/downcast-rs/1.2.0/downcast_rs/index.html#example-without-generics).

use std::{
    fmt::{Debug, Display},
    hash::Hash,
    ops::Deref,
    sync::LazyLock,
};

use combine::{between, parser, token, Parser};
use downcast_rs::{impl_downcast, Downcast};
use dyn_clone::DynClone;
use linkme::distributed_slice;
use rustc_hash::FxHashMap;

use crate::{
    common_traits::Verify,
    context::Context,
    dialect::DialectName,
    identifier::Identifier,
    input_err,
    irfmt::{
        parsers::{attr_parser, delimited_list_parser, spaced},
        printers::iter_with_sep,
    },
    location::Located,
    parsable::{Parsable, ParseResult, ParserFn, StateStream},
    printable::{self, Printable},
    result::Result,
};

#[derive(Clone)]
struct AttributeDictKeyVal {
    key: Identifier,
    val: AttrObj,
}
impl Printable for AttributeDictKeyVal {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "({}: {})", self.key, self.val.disp(ctx))
    }
}

impl Parsable for AttributeDictKeyVal {
    type Arg = ();

    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        between(
            token('('),
            token(')'),
            (Identifier::parser(()), spaced(token(':')), attr_parser()),
        )
        .map(|(key, _, val)| AttributeDictKeyVal { key, val })
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
                self.0.iter().map(|(key, val)| AttributeDictKeyVal {
                    key: key.clone(),
                    val: val.clone()
                }),
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
            .map(|key_vals| {
                AttributeDict(
                    key_vals
                        .into_iter()
                        .map(|key_val| (key_val.key, key_val.val))
                        .collect(),
                )
            })
            .parse_stream(state_stream)
            .into_result()
    }
}

/// A dictionary of attributes, mapping keys to attribute objects.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct AttributeDict(pub FxHashMap<Identifier, AttrObj>);

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
}

/// Basic functionality that every attribute in the IR must implement.
///
/// See [module](crate::attribute) documentation for more information.
pub trait Attribute: Printable + Verify + Downcast + Sync + Send + DynClone + Debug {
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

impl Verify for AttrObj {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.as_ref().verify(ctx)
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

/// Implement an Attribute Interface for an Attribute.
/// The interface trait must define a `verify` function with type [AttrInterfaceVerifier].
///
/// Usage:
/// ```
/// #[def_attribute("dialect.name")]
/// #[derive(PartialEq, Eq, Clone, Debug)]
/// struct MyAttr { }
///
/// decl_attr_interface! {
///     /// My first attribute interface.
///     MyAttrInterface {
///         fn monu(&self);
///         fn verify(attr: &dyn Attribute, ctx: &Context) -> Result<()>
///         where Self: Sized,
///         {
///              Ok(())
///         }
///     }
/// }
/// impl_attr_interface!(
///     MyAttrInterface for MyAttr
///     {
///         fn monu(&self) { println!("monu"); }
///     }
/// );
/// # use pliron::{
/// #     decl_attr_interface,
/// #     printable::{self, Printable},
/// #     context::Context, result::Result, common_traits::Verify,
/// #     attribute::Attribute, impl_attr_interface
/// # };
/// # use pliron_derive::def_attribute;
/// #
/// # impl Printable for MyAttr {
/// #    fn fmt(&self, _ctx: &Context, _state: &printable::State, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
/// #        unimplemented!()
/// #    }
/// # }
/// # pliron::impl_verify_succ!(MyAttr);
#[macro_export]
macro_rules! impl_attr_interface {
    ($intr_name:ident for $attr_name:ident { $($tt:tt)* }) => {
        $crate::type_to_trait!($attr_name, $intr_name);
        impl $intr_name for $attr_name {
            $($tt)*
        }
        const _: () = {
            #[linkme::distributed_slice(pliron::attribute::ATTR_INTERFACE_VERIFIERS)]
            static INTERFACE_VERIFIER: std::sync::LazyLock<
                (pliron::attribute::AttrId, (std::any::TypeId, pliron::attribute::AttrInterfaceVerifier))
            > =
            std::sync::LazyLock::new(||
                ($attr_name::get_attr_id_static(), (std::any::TypeId::of::<dyn $intr_name>(),
                     <$attr_name as $intr_name>::verify))
            );
        };
    };
}

/// [Attribute]s paired with every interface it implements (and the verifier for that interface).
#[distributed_slice]
pub static ATTR_INTERFACE_VERIFIERS: [LazyLock<(
    AttrId,
    (std::any::TypeId, AttrInterfaceVerifier),
)>];

/// All interfaces mapped to their super-interfaces
#[distributed_slice]
pub static ATTR_INTERFACE_DEPS: [LazyLock<(std::any::TypeId, Vec<std::any::TypeId>)>];

/// A map from every [Attribute] to its ordered (as per interface deps) list of interface verifiers.
/// An interface's super-interfaces are to be verified before it itself is.
pub static ATTR_INTERFACE_VERIFIERS_MAP: LazyLock<
    FxHashMap<AttrId, Vec<(std::any::TypeId, AttrInterfaceVerifier)>>,
> = LazyLock::new(|| {
    use std::any::TypeId;
    // Collect ATTR_INTERFACE_VERIFIERS into an [AttrId] indexed map.
    let mut attr_intr_verifiers = FxHashMap::default();
    for lazy in ATTR_INTERFACE_VERIFIERS {
        let (attr_id, (type_id, verifier)) = (**lazy).clone();
        attr_intr_verifiers
            .entry(attr_id)
            .and_modify(|verifiers: &mut Vec<(TypeId, AttrInterfaceVerifier)>| {
                verifiers.push((type_id, verifier))
            })
            .or_insert(vec![(type_id, verifier)]);
    }

    // Collect interface deps into a map.
    let interface_deps: FxHashMap<_, _> = ATTR_INTERFACE_DEPS
        .iter()
        .map(|lazy| (**lazy).clone())
        .collect();

    // Assign an integer to each interface, such that if y depends on x
    // i.e., x is a super-interface of y, then dep_sort_idx[x] < dep_sort_idx[y]
    let mut dep_sort_idx = FxHashMap::<TypeId, u32>::default();
    let mut sort_idx = 0;
    fn assign_idx_to_intr(
        interface_deps: &FxHashMap<TypeId, Vec<TypeId>>,
        dep_sort_idx: &mut FxHashMap<TypeId, u32>,
        sort_idx: &mut u32,
        intr: &TypeId,
    ) {
        if dep_sort_idx.contains_key(intr) {
            return;
        }

        // Assign index to every dependent first. We don't bother to check for cyclic
        // dependences since super interfaces are also super traits in Rust.
        let deps = interface_deps
            .get(intr)
            .expect("Expect every interface to have a (possibly empty) list of dependences");
        for dep in deps {
            assign_idx_to_intr(interface_deps, dep_sort_idx, sort_idx, dep);
        }

        // Assign an index to the current interface.
        dep_sort_idx.insert(*intr, *sort_idx);
        *sort_idx += 1;
    }

    // Assign dep_sort_idx to every interface.
    for lazy in ATTR_INTERFACE_DEPS.iter() {
        let (intr, _deps) = &**lazy;
        assign_idx_to_intr(&interface_deps, &mut dep_sort_idx, &mut sort_idx, intr);
    }

    for verifiers in attr_intr_verifiers.values_mut() {
        // sort verifiers based on its dep_sort_idx.
        verifiers.sort_by(|(a, _), (b, _)| dep_sort_idx[a].cmp(&dep_sort_idx[b]));
    }

    attr_intr_verifiers
});

/// Declare an [Attribute] interface, which can be implemented by any [Attribute].
///
/// If the interface requires any other interface to be already implemented,
/// they can be specified. The trait to which this interface is expanded will
/// have the dependent interfaces as super-traits, in addition to the [Attribute] trait
/// itself, which is always automatically added as a super-trait.
///
/// When an [Attribute] is verified, its interfaces are also automatically verified,
/// with guarantee that a super-interface is verified before an interface itself is.
///
/// Example: Here `Super1` and `Super2` are super interfaces for the interface `MyAttrIntr`.
/// ```
/// # use pliron::{decl_attr_interface, attribute::Attribute, context::Context, result::Result};
/// decl_attr_interface!(
///     Super1 {
///         fn verify(_attr: &dyn Attribute, _ctx: &Context) -> Result<()>
///         where
///             Self: Sized,
///         {
///             Ok(())
///         }
///     }
/// );
/// decl_attr_interface!(
///     Super2 {
///         fn verify(_attr: &dyn Attribute, _ctx: &Context) -> Result<()>
///         where
///             Self: Sized,
///         {
///             Ok(())
///         }
///     }
/// );
/// decl_attr_interface!(
///     /// MyAttrIntr is my best attribute interface.
///     MyAttrIntr: Super1, Super2 {
///         fn verify(_attr: &dyn Attribute, _ctx: &Context) -> Result<()>
///         where
///             Self: Sized,
///         {
///             Ok(())
///         }
///     }
/// );
/// ```
#[macro_export]
macro_rules! decl_attr_interface {
    // No deps case
    ($(#[$docs:meta])*
        $intr_name:ident { $($tt:tt)* }) => {
        decl_attr_interface!(
            $(#[$docs])*
            $intr_name: { $($tt)* }
        );
    };
    // Zero or more deps
    ($(#[$docs:meta])*
        $intr_name:ident: $($dep:path),* { $($tt:tt)* }) => {
        $(#[$docs])*
        pub trait $intr_name: pliron::attribute::Attribute $( + $dep )* {
            $($tt)*
        }
        const _: () = {
            #[linkme::distributed_slice(pliron::attribute::ATTR_INTERFACE_DEPS)]
            static ATTR_INTERFACE_DEP: std::sync::LazyLock<(std::any::TypeId, Vec<std::any::TypeId>)>
                = std::sync::LazyLock::new(|| {
                    (std::any::TypeId::of::<dyn $intr_name>(), vec![$(std::any::TypeId::of::<dyn $dep>(),)*])
             });
        };
    };
}

#[cfg(test)]
mod tests {

    use pliron::result::Result;
    use rustc_hash::{FxHashMap, FxHashSet};
    use std::any::TypeId;

    use crate::verify_err_noloc;

    use super::{ATTR_INTERFACE_DEPS, ATTR_INTERFACE_VERIFIERS_MAP};

    #[test]
    /// For every interface that an [Attr] implements, ensure that the interface verifiers
    /// get called in the right order, with super-interface verifiers called before their
    /// sub-interface verifier.
    fn check_verifiers_deps() -> Result<()> {
        // Collect interface deps into a map.
        let interface_deps: FxHashMap<_, _> = ATTR_INTERFACE_DEPS
            .iter()
            .map(|lazy| (**lazy).clone())
            .collect();

        for (attr, intrs) in ATTR_INTERFACE_VERIFIERS_MAP.iter() {
            let mut satisfied_deps = FxHashSet::<TypeId>::default();
            for (intr, _) in intrs {
                let deps = interface_deps.get(intr).ok_or_else(|| {
                    let err: Result<()> = verify_err_noloc!(
                       "Missing deps list for TypeId {:?} when checking verifier dependences for {}",
                        intr,
                        attr
                    );
                    err.unwrap_err()
                })?;
                for dep in deps {
                    if !satisfied_deps.contains(dep) {
                        return verify_err_noloc!(
                            "For {}, depencence {:?} not satisfied for {:?}",
                            attr,
                            dep,
                            intr
                        );
                    }
                }
                satisfied_deps.insert(*intr);
            }
        }

        Ok(())
    }
}
