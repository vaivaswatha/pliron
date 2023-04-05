use core::fmt;

use crate::{
    context::Context,
    error::CompilerError,
    with_context::{AttachContext, IterWithContext, WithContext},
};

// Traits for Display and Debug but with a paired Context.

///  Same as [fmt::Display], but with a [Context]. Example usage:
/// ```
/// use pliron::{with_context::*, common_traits::DisplayWithContext, context::Context};
/// use std::fmt;
/// struct S {
///     i: i64,
/// }
/// impl AttachContext for S {}
/// impl DisplayWithContext for S {
///     fn fmt(&self, _ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
///         write!(f, "{}", self.i)
///     }
/// }
///
/// let ctx = Context::new();
/// assert!(S { i: 108 }.with_ctx(&ctx).to_string() == "108");
/// ```
pub trait DisplayWithContext: AttachContext {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl<T: DisplayWithContext> fmt::Display for WithContext<'_, '_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.t.fmt(self.ctx, f)
    }
}

/// Same as [fmt::Debug], but with a [Context]. Example usage:
/// ```
/// use pliron::{with_context::*, common_traits::DebugWithContext, context::Context};
/// use std::fmt;
/// struct S {
///     i: i64,
/// }
/// impl AttachContext for S {}
/// impl DebugWithContext for S {
///     fn fmt(&self, _ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
///         write!(f, "{}", self.i)
///     }
/// }
/// fn test() {
///     let ctx = Context::new();
///     dbg!(S {i: 64 }.with_ctx(&ctx));
///     let sv = vec![S { i: 0 }, S { i: 1 }, S { i: 2 }];
///     dbg!(sv.iter().with_ctx(&ctx));
/// }
/// // Calling `test` will print:
/// // [
/// //    0,
/// //    1,
/// //    2,
/// // ]
/// ```
pub trait DebugWithContext: AttachContext {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl<T: DebugWithContext> fmt::Debug for WithContext<'_, '_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.t.fmt(self.ctx, f)
    }
}

// Implement [DebugWithContext] for any clonable [Iterator] whose [Item](Iterator::Item)
// implements [DebugWithContext].
// We need to clone the iterator because `fmt` below doesn't allow consuming it.
impl<'c, 't, T: 't + DebugWithContext, I: Iterator<Item = &'t T> + Clone> fmt::Debug
    for IterWithContext<'c, I>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// Check and ensure correctness.
pub trait Verify {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError>;
}

/// Anything that has a name.
pub trait Named {
    fn get_name(&self, ctx: &Context) -> String;
}
