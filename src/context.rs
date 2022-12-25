use crate::{
    basic_block::BasicBlock,
    dialect::{Dialect, DialectName},
    op::{OpCreator, OpId},
    operation::Operation,
    r#type::TypeObj,
    region::Region,
    storage_uniquer::{TypeValueHash, UniqueStore},
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
    /// Allocation pool for Operations.
    pub operations: ArenaCell<Operation>,
    /// Allocation pool for BasicBlocks.
    pub basic_blocks: ArenaCell<BasicBlock>,
    /// Allocation pool for Regions.
    pub regions: ArenaCell<Region>,
    /// Allocation pool for Types.
    pub types: ArenaCell<TypeObj>,
    /// A map from a type's unique hash to its's Ptr.
    pub typehash_typeptr_map: FxHashMap<TypeValueHash, Ptr<TypeObj>>,
    /// Registered dialects.
    pub dialects: FxHashMap<DialectName, Dialect>,
    /// Registered Ops.
    pub ops: FxHashMap<OpId, OpCreator>,

    pub type_store: UniqueStore<TypeObj>,
    #[cfg(test)]
    pub(crate) linked_list_store: crate::linked_list::tests::LinkedListTestArena,
}

impl Context {
    pub fn new() -> Context {
        Self::default()
    }
}

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
    /// Remove pointers to this object from other objects.
    /// Called when self is deallocated.
    fn remove_references(ptr: Ptr<Self>, ctx: &mut Context);

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
        Self::remove_references(ptr, ctx);
        Self::dealloc_sub_objects(ptr, ctx);
        Self::get_arena_mut(ctx).remove(ptr.idx);
    }
}

/// Pointer to an IR Object owned by Context.
#[derive(Debug)]
pub struct Ptr<T: ArenaObj> {
    pub(crate) idx: generational_arena::Index,
    pub(crate) _dummy: PhantomData<T>,
}

impl<'a, T: ArenaObj> Ptr<T> {
    pub fn deref(&self, ctx: &'a Context) -> Ref<'a, T> {
        T::get_arena(ctx).get(self.idx).unwrap().borrow()
    }
    pub fn deref_mut(&self, ctx: &'a Context) -> RefMut<'a, T> {
        T::get_arena(ctx).get(self.idx).unwrap().borrow_mut()
    }
}

impl<T: ArenaObj> Clone for Ptr<T> {
    fn clone(&self) -> Ptr<T> {
        Ptr {
            idx: self.idx,
            _dummy: PhantomData,
        }
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
