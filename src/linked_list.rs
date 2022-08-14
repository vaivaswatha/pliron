use crate::context::{ArenaObj, Context, Ptr};

/// Implements a linked list based on Ptr<T: ArenaObj>.
/// Types implementing this trait must provide simple
/// getters and setters that just plain update the
/// data fields in / related-to Self.
/// The default functions implement linked list operations.
trait LinkedList: ArenaObj + PartialEq {
    // Simple getter for the item previous to this in the list.
    fn get_next(&self) -> Option<Ptr<Self>>;
    // Simple getter for the item previous to this in the list.
    fn get_prev(&self) -> Option<Ptr<Self>>;
    // Simply set the item next to this in the list.
    fn set_next(&self, next: Option<Ptr<Self>>);
    // Simply set the item previous to this in the list.
    fn set_prev(&self, prev: Option<Ptr<Self>>);
    // Simply get the head of the list. Could be None if self isn't in a list.
    fn get_head(&self, ctx: &Context) -> Option<Ptr<Self>>;
    // Simply get the tail of the list. Could be None if self isn't in a list.
    fn get_tail(&self, ctx: &Context) -> Option<Ptr<Self>>;
    // Simply set the head pointer. This is usually external to the list,
    // and allows access to the first element of the list from outside.
    fn set_head(&self, ctx: &mut Context, head: Ptr<Self>);
    // Simply set the tail pointer. This is usually external to the list,
    // and allows access to the last element of the list from outside.
    fn set_tail(&self, ctx: &mut Context, tail: Ptr<Self>);

    // Insert item after self.
    fn insert_after(&self, ctx: &mut Context, item: Ptr<Self>) {
        let next = self.get_next();
        match next {
            Some(next) => {
                debug_assert!(next.deref(ctx).get_prev().unwrap() == self.get_self_ptr());
                next.deref_mut(ctx).set_prev(Some(item));
            }
            None => {
                self.set_tail(ctx, item);
            }
        }
        item.deref_mut(ctx).set_next(next);
        item.deref_mut(ctx).set_prev(Some(self.get_self_ptr()));
        self.set_next(Some(item));
    }
    fn insert_before(&self, ctx: &mut Context, item: Ptr<Self>) {
        let prev = self.get_prev();
        match prev {
            Some(prev) => {
                debug_assert!(prev.deref(ctx).get_next().unwrap() == self.get_self_ptr());
                prev.deref_mut(ctx).set_next(Some(item));
            }
            None => {
                self.set_head(ctx, item);
            }
        }
        item.deref_mut(ctx).set_prev(prev);
        item.deref_mut(ctx).set_next(Some(self.get_self_ptr()));
        self.set_prev(Some(item));
    }

}
