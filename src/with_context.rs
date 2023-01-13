//! Utilities to pair objects with [Context].

use crate::context::Context;

/// An object paired with a Context reference.
/// Idea taken from <https://stackoverflow.com/a/67761066/2128804>
#[derive(Clone)]
pub struct WithContext<'t, 'c, T> {
    pub t: &'t T,
    pub ctx: &'c Context,
}

/// Attach [Context] to any object to create a [WithContext] object.
pub trait AttachContext {
    fn with_ctx<'t, 'c>(&'t self, ctx: &'c Context) -> WithContext<'t, 'c, Self>
    where
        Self: Sized,
    {
        WithContext { t: self, ctx }
    }
}

/// [AttachContext] for iteration.
/// Maps an [Iterator] to one with a paired [Context] for each element.
#[derive(Clone)]
pub struct IterWithContext<'c, I: Iterator> {
    iter: I,
    ctx: &'c Context,
}

impl<'c, I: Iterator> IterWithContext<'c, I> {
    /// Create a new iterator that has an attached context.
    pub fn new(iter: I, ctx: &'c Context) -> Self {
        IterWithContext { iter, ctx }
    }
}

impl<'t, 'c, T: 't + AttachContext, I: Iterator<Item = &'t T>> Iterator for IterWithContext<'c, I> {
    type Item = WithContext<'t, 'c, T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|t| t.with_ctx(self.ctx))
    }
}

/// Provide an [IterWithContext] when Iterator is provided.
pub trait AttachContextWithIterator: Iterator {
    fn with_ctx(self, ctx: &Context) -> IterWithContext<Self>
    where
        Self: Sized,
    {
        IterWithContext::new(self, ctx)
    }
}

/// For every [Iterator] whose [Item](Iterator::Item) implements [AttachContext],
/// implement [AttachContextWithIterator].
impl<'t, T: 't + AttachContext, I: Iterator<Item = &'t T>> AttachContextWithIterator for I {}
