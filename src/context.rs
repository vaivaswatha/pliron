use generational_arena::Arena;

use crate::{
    basic_block::BasicBlock,
    operation::Operation,
    r#type::{TypeHash, TypeObj},
};
use std::{
    any::TypeId,
    cell::{Ref, RefCell, RefMut},
    collections::HashMap,
    hash::Hash,
    marker::PhantomData,
};

pub type ArenaCell<T> = Arena<RefCell<T>>;

#[derive(Default)]
pub struct Context {
    // Allocation pool for Operations.
    pub operations: ArenaCell<Operation>,
    // Allocation pool for BasicBlocks.
    pub basic_blocks: ArenaCell<BasicBlock>,
    // Allocation pool for Types.
    pub types: ArenaCell<TypeObj>,
    // A map from a type's unique hash to its's Ptr.
    pub typehash_typeptr_map: HashMap<TypeHash, Ptr<TypeObj>>,
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
    // Get the arena that has allocated this object.
    fn get_arena(ctx: &Context) -> &ArenaCell<Self>;
    // Get the arena that has allocated this object.
    fn get_arena_mut(ctx: &mut Context) -> &mut ArenaCell<Self>;
    // Get a Ptr to self.
    fn get_self_ptr(&self, ctx: &Context) -> Ptr<Self>;
    // If this object contains any ArenaObj itself, it must dealloc()
    // all of those sub-objects. This is called when self is deallocated.
    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context);
    // Remove pointers to this object from other objects.
    // Called when self is deallocated.
    fn remove_references(ptr: Ptr<Self>, ctx: &mut Context);

    // Allocates object on the arena, given a creator function.
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

    // Deallocates this object from the arena.
    fn dealloc(ptr: Ptr<Self>, ctx: &mut Context) {
        Self::remove_references(ptr, ctx);
        Self::dealloc_sub_objects(ptr, ctx);
        Self::get_arena_mut(ctx).remove(ptr.idx);
    }
}

// Pointer to an IR Object owned by Context.
#[derive(Debug)]
pub struct Ptr<T: ArenaObj> {
    idx: generational_arena::Index,
    _dummy: PhantomData<T>,
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

impl<T: ArenaObj + 'static> Hash for Ptr<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        TypeId::of::<T>().hash(state);
        self.idx.hash(state);
    }
}
