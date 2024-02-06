//! [Context] and [Ptr] together provide memory management for `pliron`.

use crate::{
    basic_block::BasicBlock,
    common_traits::Verify,
    dialect::{Dialect, DialectName},
    error::Result,
    op::{OpCreator, OpId},
    operation::Operation,
    printable::{self, Printable},
    r#type::TypeObj,
    region::Region,
    storage_uniquer::UniqueStore,
    uniqued_any::UniquedAny,
};
use rustc_hash::FxHashMap;
use std::{
    any::TypeId,
    cell::{Ref, RefCell, RefMut},
    hash::Hash,
    marker::PhantomData,
};

pub type ArenaCell<T> = generational_arena::Arena<RefCell<T>>;
pub type ArenaIndex = generational_arena::Index;

/// A context stores all IR data of this compilation session.
#[derive(Default)]
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
    pub type_store: UniqueStore<TypeObj>,
    /// Storage for other uniqued objects.
    pub(crate) uniqued_any_store: UniqueStore<UniquedAny>,

    #[cfg(test)]
    pub(crate) linked_list_store: crate::linked_list::tests::LinkedListTestArena,
}

impl Context {
    pub fn new() -> Context {
        Self::default()
    }
}

pub(crate) mod private {
    use std::{cell::RefCell, marker::PhantomData};

    use super::{ArenaCell, Context, Ptr};

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
            let creator = |idx: generational_arena::Index| {
                let t = f(Ptr::<Self> {
                    idx,
                    _dummy: PhantomData::<Self>,
                });
                RefCell::new(t)
            };
            Ptr::<Self> {
                idx: Self::get_arena_mut(ctx).insert_with(creator),
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
    pub(crate) idx: generational_arena::Index,
    pub(crate) _dummy: PhantomData<T>,
}

impl<'a, T: ArenaObj> Ptr<T> {
    /// Return a [Ref] to the pointee.
    /// This borrows from a RefCell and the borrow is live
    /// as long as the returned Ref lives.
    pub fn deref(&self, ctx: &'a Context) -> Ref<'a, T> {
        T::get_arena(ctx).get(self.idx).unwrap().borrow()
    }

    /// Return a RefMut to the pointee.
    /// This mutably borrows from a RefCell and the borrow is live
    /// as long as the returned RefMut lives.
    pub fn deref_mut(&self, ctx: &'a Context) -> RefMut<'a, T> {
        T::get_arena(ctx).get(self.idx).unwrap().borrow_mut()
    }

    /// Try and return a Ref to the pointee.
    /// This borrows from a RefCell and the borrow is live
    /// as long as the returned Ref lives.
    pub fn try_deref(&self, ctx: &'a Context) -> Option<Ref<'a, T>> {
        T::get_arena(ctx).get(self.idx).unwrap().try_borrow().ok()
    }

    /// Try and return a RefMut to the pointee.
    /// This mutably borrows from a RefCell and the borrow is live
    /// as long as the returned RefMut lives.
    pub fn try_deref_mut(&self, ctx: &'a Context) -> Option<RefMut<'a, T>> {
        T::get_arena(ctx)
            .get(self.idx)
            .unwrap()
            .try_borrow_mut()
            .ok()
    }

    /// Create a unique (to the arena) name based on the arena index.
    pub(crate) fn make_name(&self, name_base: &str) -> String {
        let idx = self.idx.into_raw_parts();
        name_base.to_string() + "_" + &idx.0.to_string() + "_" + &idx.1.to_string()
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
