//! [Context] and [Ptr] together provide memory management for `pliron`.

use crate::{
    basic_block::BasicBlock,
    common_traits::Verify,
    dialect::{Dialect, DialectName},
    identifier::Identifier,
    op::{OpCreator, OpId},
    operation::Operation,
    printable::{self, Printable},
    region::Region,
    result::Result,
    storage_uniquer::UniqueStore,
    r#type::TypeObj,
    uniqued_any::UniquedAny,
};
use linkme::distributed_slice;
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

// pub type ArenaIndex = slotmap::DefaultKey;
pub type ArenaCell<T> = SlotMap<ArenaIndex, RefCell<T>>;

/// A context stores all IR data of this compilation session.
pub struct Context {
    /// Allocation pool for [Operation]s.
    pub operations: ArenaCell<Operation>,
    /// Allocation pool for [BasicBlock]s.
    pub basic_blocks: ArenaCell<BasicBlock>,
    /// Allocation pool for [Region]s.
    pub regions: ArenaCell<Region>,
    /// Registered [Dialect]s.
    pub dialects: FxHashMap<DialectName, Dialect>,
    /// Registered [Op](crate::op::Op)s.
    pub ops: FxHashMap<OpId, OpCreator>,
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
}

impl Default for Context {
    fn default() -> Self {
        let ctx = Context {
            operations: ArenaCell::default(),
            basic_blocks: ArenaCell::default(),
            regions: ArenaCell::default(),
            dialects: FxHashMap::default(),
            ops: FxHashMap::default(),
            type_store: UniqueStore::default(),
            uniqued_any_store: UniqueStore::default(),
            aux_data: SlotMap::with_key(),
            aux_data_map: FxHashMap::default(),

            #[cfg(test)]
            linked_list_store: crate::linked_list::tests::LinkedListTestArena::default(),
        };
        verify_dict_keys();
        ctx
    }
}

pub(crate) mod private {
    use std::{cell::RefCell, marker::PhantomData};

    use super::{ArenaCell, ArenaIndex, Context, Ptr};

    /// An IR object owned by Context
    pub trait ArenaObj
    where
        Self: Sized,
    {
        /// Get the arena that has allocated this object.
        fn get_arena(ctx: &Context) -> &ArenaCell<Self>;
        /// Get the arena that has allocated this object.
        fn get_arena_mut(ctx: &mut Context) -> &mut ArenaCell<Self>;
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
    pub fn deref(&self, ctx: &'a Context) -> Ref<'a, T> {
        T::get_arena(ctx)
            .get(self.idx)
            .expect("Dangling Ptr deref")
            .borrow()
    }

    /// Return a RefMut to the pointee.
    /// This mutably borrows from a RefCell and the borrow is live
    /// as long as the returned RefMut lives.
    pub fn deref_mut(&self, ctx: &'a Context) -> RefMut<'a, T> {
        T::get_arena(ctx)
            .get(self.idx)
            .expect("Dangling Ptr deref_mut")
            .borrow_mut()
    }

    /// Try and return a Ref to the pointee.
    /// This borrows from a RefCell and the borrow is live
    /// as long as the returned Ref lives.
    pub fn try_deref(&self, ctx: &'a Context) -> Option<Ref<'a, T>> {
        T::get_arena(ctx)
            .get(self.idx)
            .expect("Dangling Ptr deref")
            .try_borrow()
            .ok()
    }

    /// Try and return a RefMut to the pointee.
    /// This mutably borrows from a RefCell and the borrow is live
    /// as long as the returned RefMut lives.
    pub fn try_deref_mut(&self, ctx: &'a Context) -> Option<RefMut<'a, T>> {
        T::get_arena(ctx)
            .get(self.idx)
            .expect("Dangling Ptr deref_mut")
            .try_borrow_mut()
            .ok()
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
#[derive(Hash, Eq, PartialEq, Debug, Clone)]
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

#[doc(hidden)]
/// `pliron` uses dictionaries indexed by static [Identifier]s in many places,
/// such as [Context::aux_data_map], and the states of [Printable](crate::printable::State)
/// and [Parsable](crate::parsable::State). To avoid collisions in these [Identifier]s,
/// we use the [placeholder] macro to verify that all such keys declared using the macro
/// are unique. The macro adds the keys to this static slice, which is then verified
/// when a [Context] is created.
#[distributed_slice]
pub static DICT_KEY_IDS: [LazyLock<DictKeyId>];

/// Verify that all dictionary keys are unique. This is called when a [Context] is created.
/// If any duplicate keys are found, a panic is raised with the file, line, and column
/// information of the duplicate keys.
pub fn verify_dict_keys() {
    let mut seen: FxHashMap<Identifier, (&'static str, u32, u32)> = FxHashMap::default();
    for key in DICT_KEY_IDS.iter() {
        if let Some((file, line, column)) = seen.get(&key.id) {
            panic!(
                "Duplicate dictionary key \"{}\" declared in {}:{}:{} and {}:{}:{}",
                key.id, file, line, column, key.file, key.line, key.column
            );
        }
        seen.insert(key.id.clone(), (key.file, key.line, key.column));
    }
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
            #[linkme::distributed_slice(::pliron::context::DICT_KEY_IDS)]
            pub static $decl: std::sync::LazyLock<::pliron::context::DictKeyId> =
                std::sync::LazyLock::new(|| ::pliron::context::DictKeyId {
                    id: $name.try_into().unwrap(),
                    file: file!(),
                    line: line!(),
                    column: column!(),
                });
        };
        $(#[$outer])*
        // Create a static variable with the provided name to access the identifier.
        pub static $decl: std::sync::LazyLock<::pliron::identifier::Identifier> =
            std::sync::LazyLock::new(|| $name.try_into().unwrap());
    };
}
