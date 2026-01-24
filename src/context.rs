//! [Context] and [Ptr] together provide memory management for `pliron`.

use crate::{
    basic_block::BasicBlock,
    common_traits::Verify,
    dialect::{Dialect, DialectName},
    identifier::Identifier,
    input_error_noloc,
    operation::Operation,
    printable::{self, Printable},
    region::Region,
    result::Result,
    storage_uniquer::UniqueStore,
    r#type::TypeObj,
    uniqued_any::UniquedAny,
    verify_err_noloc,
};
use rustc_hash::FxHashMap;
use slotmap::{SlotMap, new_key_type};
use std::{
    any::{Any, TypeId},
    cell::{Ref, RefCell, RefMut},
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
    sync::LazyLock,
};

new_key_type! {
    /// The index type for the [SlotMap] used to store IR objects.
    pub struct ArenaIndex;
}

new_key_type! {
    /// The index type for the [SlotMap] used to store auxiliary data.
    pub struct AuxDataIndex;
}

impl Display for ArenaIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// An arena allocation pool for IR objects.
pub type Arena<T> = SlotMap<ArenaIndex, RefCell<T>>;

/// A context stores all IR data of this compilation session.
pub struct Context {
    /// Allocation pool for [Operation]s.
    pub(crate) operations: Arena<Operation>,
    /// Allocation pool for [BasicBlock]s.
    pub(crate) basic_blocks: Arena<BasicBlock>,
    /// Allocation pool for [Region]s.
    pub(crate) regions: Arena<Region>,
    /// Registered [Dialect]s.
    pub(crate) dialects: FxHashMap<DialectName, Dialect>,
    /// Storage for uniqued [TypeObj]s.
    pub(crate) type_store: UniqueStore<TypeObj>,
    /// Storage for other uniqued objects.
    pub(crate) uniqued_any_store: UniqueStore<UniquedAny>,
    /// Arbitrary data storage. Use [Self::aux_data_map] for dictionary access.
    pub aux_data: SlotMap<AuxDataIndex, Box<dyn Any>>,
    /// A dictionary with keys mapping to an index in [Self::aux_data].
    pub aux_data_map: FxHashMap<Identifier, AuxDataIndex>,

    #[cfg(test)]
    pub(crate) linked_list_store: crate::linked_list::tests::LinkedListTestArena,
}

impl Context {
    pub fn new() -> Context {
        Self::default()
    }

    /// Is the IR in this context empty?
    /// An IR is considered empty if it has no operations, basic blocks, or regions.
    /// This does not check for types, dialects, ops, or aux_data stored in the context.
    pub fn is_ir_empty(&self) -> bool {
        self.operations.is_empty() && self.basic_blocks.is_empty() && self.regions.is_empty()
    }
}

impl Default for Context {
    fn default() -> Self {
        let mut ctx = Context {
            operations: Arena::default(),
            basic_blocks: Arena::default(),
            regions: Arena::default(),
            dialects: FxHashMap::default(),
            type_store: UniqueStore::default(),
            uniqued_any_store: UniqueStore::default(),
            aux_data: SlotMap::with_key(),
            aux_data_map: FxHashMap::default(),

            #[cfg(test)]
            linked_list_store: crate::linked_list::tests::LinkedListTestArena::default(),
        };

        // Verify that all dictionary keys are unique.
        if let Err(err) = &*DICT_KEYS_VERIFIER {
            panic!("{}", err.err);
        }

        // Run all context registrations
        for registration in get_context_registrations() {
            registration(&mut ctx);
        }

        ctx
    }
}

pub(crate) mod private {
    use std::{cell::RefCell, marker::PhantomData};

    use super::{Arena, ArenaIndex, Context, Ptr};

    /// An IR object owned by Context
    pub trait ArenaObj
    where
        Self: Sized,
    {
        /// Get the arena that has allocated this object.
        fn get_arena(ctx: &Context) -> &Arena<Self>;
        /// Get the arena that has allocated this object.
        fn get_arena_mut(ctx: &mut Context) -> &mut Arena<Self>;
        /// Get a Ptr to self.
        fn get_self_ptr(&self, ctx: &Context) -> Ptr<Self>;
        /// If this object contains any ArenaObj itself, it must dealloc()
        /// all of those sub-objects. This is called when self is deallocated.
        fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context);

        /// Allocates object on the arena, given a creator function.
        fn alloc<T: FnOnce(Ptr<Self>) -> Self>(ctx: &mut Context, f: T) -> Ptr<Self> {
            let creator = |idx: ArenaIndex| {
                let t = f(Ptr::<Self> {
                    idx,
                    _dummy: PhantomData::<Self>,
                });
                RefCell::new(t)
            };
            Ptr::<Self> {
                idx: Self::get_arena_mut(ctx).insert_with_key(creator),
                _dummy: PhantomData,
            }
        }

        /// Deallocates this object from the arena.
        fn dealloc(ptr: Ptr<Self>, ctx: &mut Context) {
            Self::dealloc_sub_objects(ptr, ctx);
            Self::get_arena_mut(ctx).remove(ptr.idx);
        }
    }
}

use private::ArenaObj;

/// Pointer to an IR Object owned by Context.
#[derive(Debug)]
pub struct Ptr<T: ArenaObj> {
    pub(crate) idx: ArenaIndex,
    pub(crate) _dummy: PhantomData<T>,
}

impl<'a, T: ArenaObj> Ptr<T> {
    /// Return a [Ref] to the pointee.
    /// This borrows from a RefCell and the borrow is live
    /// as long as the returned Ref lives.
    /// Run `cargo` with options `+nightly -Zbuild-std -Zbuild-std-features="debug_refcell"`
    /// to enable printing the interior mutability violation locations.
    #[track_caller]
    pub fn deref(&self, ctx: &'a Context) -> Ref<'a, T> {
        T::get_arena(ctx)
            .get(self.idx)
            .expect("Dangling Ptr deref")
            .borrow()
    }

    /// Return a RefMut to the pointee.
    /// This mutably borrows from a RefCell and the borrow is live
    /// as long as the returned RefMut lives.
    /// Run `cargo` with options `+nightly -Zbuild-std -Zbuild-std-features="debug_refcell"`
    /// to enable printing the interior mutability violation locations.
    #[track_caller]
    pub fn deref_mut(&self, ctx: &'a Context) -> RefMut<'a, T> {
        T::get_arena(ctx)
            .get(self.idx)
            .expect("Dangling Ptr deref_mut")
            .borrow_mut()
    }

    /// Try and return a Ref to the pointee.
    /// This borrows from a RefCell and the borrow is live
    /// as long as the returned Ref lives.
    pub fn try_deref(&self, ctx: &'a Context) -> Result<Ref<'a, T>> {
        T::get_arena(ctx)
            .get(self.idx)
            .expect("Dangling Ptr deref")
            .try_borrow()
            .map_err(|err| input_error_noloc!(err))
    }

    /// Try and return a RefMut to the pointee.
    /// This mutably borrows from a RefCell and the borrow is live
    /// as long as the returned RefMut lives.
    pub fn try_deref_mut(&self, ctx: &'a Context) -> Result<RefMut<'a, T>> {
        T::get_arena(ctx)
            .get(self.idx)
            .expect("Dangling Ptr deref_mut")
            .try_borrow_mut()
            .map_err(|err| input_error_noloc!(err))
    }

    /// Create a unique (to the arena) name based on the arena index.
    pub(crate) fn make_name(&self, name_base: &str) -> Identifier {
        let idx = format!("{}", self.idx);
        (name_base.to_string() + &idx).try_into().unwrap()
    }
}

impl<T: ArenaObj> Clone for Ptr<T> {
    fn clone(&self) -> Ptr<T> {
        *self
    }
}

impl<T: ArenaObj> Copy for Ptr<T> {}

impl<T: ArenaObj> PartialEq for Ptr<T> {
    fn eq(&self, other: &Self) -> bool {
        self.idx == other.idx
    }
}

impl<T: ArenaObj> Eq for Ptr<T> {}

impl<T: ArenaObj + 'static> Hash for Ptr<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        TypeId::of::<T>().hash(state);
        self.idx.hash(state);
    }
}

impl<T: ArenaObj + Printable> Printable for Ptr<T> {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        self.deref(ctx).fmt(ctx, state, f)
    }
}

impl<T: ArenaObj + Verify> Verify for Ptr<T> {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.deref(ctx).verify(ctx)
    }
}

#[doc(hidden)]
/// Declaration of a static [Identifier] for use as a dictionary key.
#[derive(Eq, PartialEq, Debug, Clone)]
pub struct DictKeyId {
    /// The [Identifier] itself.
    pub id: Identifier,
    /// The file where this key was declared.
    pub file: &'static str,
    /// The line where this key was declared.
    pub line: u32,
    /// The column where this key was declared.
    pub column: u32,
}

/// These represent registrations that happen automatically at link time.
/// Every dialect, op, type, and attribute that are linked into your code
/// will register themselves using this type.
pub type ContextRegistration = fn(&mut Context);

#[doc(hidden)]
/// `pliron` uses dictionaries indexed by static [Identifier]s in many places,
/// such as [Context::aux_data_map], and the states of [Printable](crate::printable::State)
/// and [Parsable](crate::parsable::State). To avoid collisions in these [Identifier]s,
/// we use the [crate::dict_key!] macro to verify that all such keys declared using the macro
/// are unique. The macro adds the keys to this static slice, which is then verified
/// when a [Context] is created.
#[cfg(not(target_family = "wasm"))]
pub mod statics {
    use super::*;

    #[::pliron::linkme::distributed_slice]
    #[linkme(crate = ::pliron::linkme)]
    pub static DICT_KEY_IDS: [LazyLock<DictKeyId>];

    pub fn get_dict_key_ids() -> impl Iterator<Item = &'static LazyLock<DictKeyId>> {
        DICT_KEY_IDS.iter()
    }

    #[::pliron::linkme::distributed_slice]
    #[linkme(crate = ::pliron::linkme)]
    pub static CONTEXT_REGISTRATIONS: [LazyLock<ContextRegistration>];

    pub fn get_context_registrations()
    -> impl Iterator<Item = &'static LazyLock<ContextRegistration>> {
        CONTEXT_REGISTRATIONS.iter()
    }
}

#[cfg(target_family = "wasm")]
pub mod statics {
    use super::*;
    use crate::utils::inventory::LazyLockWrapper;

    ::pliron::inventory::collect!(LazyLockWrapper<DictKeyId>);

    pub fn get_dict_key_ids() -> impl Iterator<Item = &'static LazyLock<DictKeyId>> {
        ::pliron::inventory::iter::<LazyLockWrapper<DictKeyId>>().map(|llw| llw.0)
    }

    ::pliron::inventory::collect!(LazyLockWrapper<ContextRegistration>);

    pub fn get_context_registrations()
    -> impl Iterator<Item = &'static LazyLock<ContextRegistration>> {
        ::pliron::inventory::iter::<LazyLockWrapper<ContextRegistration>>().map(|llw| llw.0)
    }
}

pub use statics::*;

#[doc(hidden)]
pub static DICT_KEYS_VERIFIER: LazyLock<Result<()>> = LazyLock::new(verify_dict_keys);

#[doc(hidden)]
/// Verify that all dictionary keys are unique. This is called when a [Context] is created.
/// If any duplicate keys are found, a panic is raised with the file, line, and column
/// information of the duplicate keys.
pub fn verify_dict_keys() -> Result<()> {
    let mut seen: FxHashMap<Identifier, (&'static str, u32, u32)> = FxHashMap::default();
    for key in get_dict_key_ids() {
        if let Some((file, line, column)) = seen.get(&key.id) {
            return verify_err_noloc!(
                "Duplicate dictionary key \"{}\" declared in {}:{}:{} and {}:{}:{}",
                key.id,
                file,
                line,
                column,
                key.file,
                key.line,
                key.column
            );
        }
        seen.insert(key.id.clone(), (key.file, key.line, key.column));
    }
    Ok(())
}

/// A macro to declare a static [Identifier] for use as a dictionary key.
///
/// Usage:
/// ```
/// # use pliron::dict_key;
/// dict_key!(MY_KEY, "my_key");
/// let mut ctx = pliron::context::Context::new();
/// let aux_data_index = ctx.aux_data.insert(Box::new(42));
/// ctx.aux_data_map.insert(MY_KEY.clone(), aux_data_index);
/// assert_eq!(ctx.aux_data[aux_data_index].downcast_ref::<i32>(), Some(&42));
/// assert_eq!(ctx.aux_data_map[&*MY_KEY], aux_data_index);
/// ```
/// Here, `MY_KEY` is the name of the static variable, and `"my_key"` is the
/// string value of the [Identifier]. The macro will create a static variable
/// of type [`LazyLock<Identifier>`](LazyLock) with the name `MY_KEY`.
#[macro_export]
macro_rules! dict_key {
    (   $(#[$outer:meta])*
        $decl:ident, $name:expr
    ) => {
        // Create a static variable linked to the DICT_KEY_IDS slice
        // to ensure that all keys are unique.
        // The static variable is created in a separate anonmyous module.
        const _: () = {
            #[cfg_attr(not(target_family = "wasm"),
                ::pliron::linkme::distributed_slice(::pliron::context::DICT_KEY_IDS), linkme(crate = ::pliron::linkme))]
            pub static $decl: std::sync::LazyLock<::pliron::context::DictKeyId> =
                std::sync::LazyLock::new(|| ::pliron::context::DictKeyId {
                    id: $name.try_into().unwrap(),
                    file: file!(),
                    line: line!(),
                    column: column!(),
                });

            #[cfg(target_family = "wasm")]
            ::pliron::inventory::submit! {
                ::pliron::utils::inventory::LazyLockWrapper(&$decl)
            }
        };
        $(#[$outer])*
        // Create a static variable with the provided name to access the identifier.
        pub static $decl: std::sync::LazyLock<::pliron::identifier::Identifier> =
            std::sync::LazyLock::new(|| $name.try_into().unwrap());
    };
}
