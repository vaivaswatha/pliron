use crate::context::{ArenaObj, Context, Ptr};

/// An object that contains a linked list.
pub trait ContainsLinkedList<T: LinkedList> {
    /// Simply get the head of the list.
    fn get_head(&self) -> Option<Ptr<T>>;
    /// Simply get the tail of the list.
    fn get_tail(&self) -> Option<Ptr<T>>;
    /// Simply set the head pointer.
    fn set_head(&mut self, head: Option<Ptr<T>>);
    /// Simply set the tail pointer
    fn set_tail(&mut self, tail: Option<Ptr<T>>);
}

/// Implements a linked list based on [Ptr]
/// Types implementing this trait must provide simple
/// getters and setters for prev and next fields.
/// The default functions implement linked list operations.
pub trait LinkedList: ArenaObj + PartialEq {
    type ContainerType: ContainsLinkedList<Self> + ArenaObj;

    /// Simple getter for the item previous to this in the list.
    fn get_next(&self) -> Option<Ptr<Self>>;
    /// Simple getter for the item previous to this in the list.
    fn get_prev(&self) -> Option<Ptr<Self>>;
    /// Simply set the item next to this in the list.
    fn set_next(&mut self, next: Option<Ptr<Self>>);
    /// Simply set the item previous to this in the list.
    fn set_prev(&mut self, prev: Option<Ptr<Self>>);
    /// Get a reference to the object that contains this linked list.
    fn get_container(&self) -> Option<Ptr<Self::ContainerType>>;
    /// Set the container for this node.
    fn set_container(&mut self, container: Option<Ptr<Self::ContainerType>>);

    /// Insert self after mark.
    fn insert_after(&mut self, ctx: &Context, mark: Ptr<Self>) {
        debug_assert!(
            self.get_prev().is_none()
                && self.get_next().is_none()
                && self.get_container().is_none(),
            "LinkedList node must be unlinked before relinking"
        );
        let mut mark_ref = mark.deref_mut(ctx);
        let container = mark_ref.get_container().unwrap();
        let next = mark_ref.get_next();
        match next {
            Some(next) => {
                debug_assert!(next.deref(ctx).get_prev().unwrap() == mark);
                next.deref_mut(ctx).set_prev(Some(self.get_self_ptr(ctx)));
            }
            None => {
                debug_assert!(container.deref(ctx).get_tail().unwrap() == mark);
                container
                    .deref_mut(ctx)
                    .set_tail(Some(self.get_self_ptr(ctx)));
            }
        }
        self.set_next(next);
        self.set_prev(Some(mark));
        (*mark_ref).set_next(Some(self.get_self_ptr(ctx)));
        self.set_container(Some(container));
    }

    /// Insert self before mark.
    fn insert_before(&mut self, ctx: &Context, mark: Ptr<Self>) {
        debug_assert!(
            self.get_prev().is_none()
                && self.get_next().is_none()
                && self.get_container().is_none(),
            "LinkedList node must be unlinked before relinking"
        );
        let mut mark_ref = mark.deref_mut(ctx);
        let container = mark_ref.get_container().unwrap();
        let prev = mark_ref.get_prev();
        match prev {
            Some(prev) => {
                debug_assert!(
                    prev.deref(ctx).get_next().unwrap() == mark.deref(ctx).get_self_ptr(ctx)
                );
                prev.deref_mut(ctx).set_next(Some(self.get_self_ptr(ctx)));
            }
            None => {
                debug_assert!(container.deref(ctx).get_head().unwrap() == mark);
                container
                    .deref_mut(ctx)
                    .set_head(Some(self.get_self_ptr(ctx)));
            }
        }
        self.set_prev(prev);
        self.set_next(Some(mark.deref(ctx).get_self_ptr(ctx)));
        (*mark_ref).set_prev(Some(self.get_self_ptr(ctx)));
        self.set_container(Some(container));
    }

    /// Insert self as the head of the list.
    fn insert_at_front(&mut self, container: Ptr<Self::ContainerType>, ctx: &Context) {
        debug_assert!(
            self.get_prev().is_none()
                && self.get_next().is_none()
                && self.get_container().is_none(),
            "LinkedList node must be unlinked before relinking"
        );
        let mut container_ref = container.deref_mut(ctx);
        let head = container_ref.get_head();
        match head {
            Some(head) => {
                debug_assert!(head.deref(ctx).get_prev().is_none());
                head.deref_mut(ctx).set_prev(Some(self.get_self_ptr(ctx)))
            }
            None => {
                container_ref.set_tail(Some(self.get_self_ptr(ctx)));
            }
        }
        self.set_next(head);
        container_ref.set_head(Some(self.get_self_ptr(ctx)));
        self.set_container(Some(container));
    }

    /// Insert self as the tail of the list.
    fn insert_at_back(&mut self, container: Ptr<Self::ContainerType>, ctx: &Context) {
        debug_assert!(
            self.get_prev().is_none()
                && self.get_next().is_none()
                && self.get_container().is_none(),
            "LinkedList node must be unlinked before relinking"
        );
        let mut container_ref = container.deref_mut(ctx);
        let tail = container_ref.get_tail();
        match tail {
            Some(tail) => {
                debug_assert!(tail.deref(ctx).get_next().is_none());
                tail.deref_mut(ctx).set_next(Some(self.get_self_ptr(ctx)));
            }
            None => {
                container_ref.set_head(Some(self.get_self_ptr(ctx)));
            }
        }
        self.set_prev(tail);
        container_ref.set_tail(Some(self.get_self_ptr(ctx)));
        self.set_container(Some(container));
    }

    /// Unlink self from list.
    fn remove(&mut self, ctx: &Context) {
        let container = self.get_container();
        debug_assert!(
            container.is_some(),
            "LinkedList: Attempt to remove unlinked node"
        );
        match self.get_next() {
            Some(next) => next.deref_mut(ctx).set_prev(self.get_prev()),
            None => {
                container.unwrap().deref_mut(ctx).set_tail(self.get_prev());
            }
        }
        match self.get_prev() {
            Some(prev) => {
                prev.deref_mut(ctx).set_prev(self.get_next());
            }
            None => {
                container.unwrap().deref_mut(ctx).set_head(self.get_next());
            }
        }
        self.set_next(None);
        self.set_prev(None);
        self.set_container(None);
    }
}
