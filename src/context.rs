use crate::operation::Operation;
use std::{
    cell::{Ref, RefCell, RefMut},
    marker::PhantomData,
};

pub type ArenaCell<T> = generational_arena::Arena<RefCell<T>>;

pub struct Context {
    // Allocation pool for Operations.
    pub operations: ArenaCell<Operation>,
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
    fn get_self_ptr(&self) -> Ptr<Self>;
    // If this object contains any ArenaObj itself, it must dealloc()
    // all of those sub-objects. This is called when self is deallocated.
    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context);
    // Remove pointers to this object from other objects.
    // Called when self is deallocated.
    fn remove_references(ptr: Ptr<Self>, ctx: &mut Context);

    // Allocates object on the arena, given a creator function.
    fn alloc<T: Fn(Ptr<Self>) -> Self>(ctx: &mut Context, f: T) -> Ptr<Self> {
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
    fn dealloc(ptr: Ptr<Self>, ctx: &mut Context) {
        Self::remove_references(ptr.clone(), ctx);
        Self::dealloc_sub_objects(ptr.clone(), ctx);
        Self::get_arena_mut(ctx).remove(ptr.idx);
    }
}

// Pointer to an IR Object owned by Context.
#[derive(Debug, PartialEq)]
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

impl<'a, T: ArenaObj> Clone for Ptr<T> {
    fn clone(&self) -> Ptr<T> {
        Ptr {
            idx: self.idx,
            _dummy: PhantomData,
        }
    }
}

impl<'a, T: ArenaObj> Copy for Ptr<T> {}
