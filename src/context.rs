use crate::operation::Operation;
use std::marker::PhantomData;

pub struct Context {
    // Allocation pool for Operations.
    pub operations: generational_arena::Arena<Operation>,
}

/// An IR object owned by Context
pub trait ArenaObj
where
    Self: Sized,
{
    // Get the arena that has allocated this object.
    fn get_arena(ctx: &Context) -> &generational_arena::Arena<Self>;
    // Get the arena that has allocated this object.
    fn get_arena_mut(ctx: &mut Context) -> &mut generational_arena::Arena<Self>;
    // If this object contains any ArenaObj itself, it must dealloc()
    // all of those sub-objects. This is called when self is deallocated.
    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context);
    // Are there pointers to this object from other objects?
    // This is asserted during dealloc.
    fn has_references(ptr: Ptr<Self>, ctx: &Context) -> bool;

    // Allocates object on the arena, given a creator function.
    fn alloc<T: Fn(Ptr<Self>) -> Self>(ctx: &mut Context, f: T) -> Ptr<Self> {
        let creator = |idx: generational_arena::Index| {
            f(Ptr::<Self> {
                idx,
                _dummy: PhantomData::<Self>,
            })
        };
        Ptr::<Self> {
            idx: Self::get_arena_mut(ctx).insert_with(creator),
            _dummy: PhantomData,
        }
    }
    fn dealloc(ptr: Ptr<Self>, ctx: &mut Context) {
        debug_assert!(Self::has_references(ptr.clone(), ctx));
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
    pub fn deref(&'a self, ctx: &'a Context) -> &'a T {
        T::get_arena(ctx).get(self.idx).unwrap()
    }
    pub fn deref_mut(&'a self, ctx: &'a mut Context) -> &'a mut T {
        T::get_arena_mut(ctx).get_mut(self.idx).unwrap()
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
