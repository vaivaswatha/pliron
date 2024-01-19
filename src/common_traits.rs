//! Utility traits such as [Named], [Verify] etc.

use crate::{context::Context, error::Result};

/// Check and ensure correctness.
pub trait Verify {
    fn verify(&self, ctx: &Context) -> Result<()>;
}

/// Anything that has a name.
pub trait Named {
    // A (not necessarily unique) name.
    fn given_name(&self, ctx: &Context) -> Option<String>;
    // A Unique (within the context) ID.
    fn id(&self, ctx: &Context) -> String;
    // A unique name; concatenation of name and id.
    fn unique_name(&self, ctx: &Context) -> String {
        match self.given_name(ctx) {
            Some(given_name) => given_name + "_" + &self.id(ctx),
            None => self.id(ctx),
        }
    }
}

/// For types that are a reference-counted container,
/// provides methods to [share](Self::share) (i.e., [Rc::clone](std::rc::Rc::clone))
/// and [deep copy](Self::replicate) inner data.
/// This just avoids ambiguity over using `Rc::clone`, which doesn't clone
/// inner data but increases the reference count.
pub trait RcSharable {
    /// Light weight (reference counted) clone.
    fn share(&self) -> Self;

    /// New copy that doesn't share the internal state of self.
    fn replicate(&self) -> Self;
}
