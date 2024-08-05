//! Utility traits such as [Named], [Verify] etc.

use crate::{
    context::Context,
    identifier::{underscore, Identifier},
    result::Result,
};

/// Check and ensure correctness.
pub trait Verify {
    fn verify(&self, ctx: &Context) -> Result<()>;
}

/// Sugar to implement a verifier that always succeeds.
/// Usage:
/// ```
/// # use pliron::{impl_verify_succ, context::Context, common_traits::Verify};
/// struct A;
/// impl_verify_succ!(A);
/// let a = A;
/// let ctx = Context::new();
/// assert!(a.verify(&ctx).is_ok());
/// ```
#[macro_export]
macro_rules! impl_verify_succ {
    ($op_name:path) => {
        impl $crate::common_traits::Verify for $op_name {
            fn verify(&self, _ctx: &$crate::context::Context) -> $crate::result::Result<()> {
                Ok(())
            }
        }
    };
}

/// Anything that has a name.
pub trait Named {
    // A (not necessarily unique) name.
    fn given_name(&self, ctx: &Context) -> Option<Identifier>;
    // A Unique (within the context) ID.
    fn id(&self, ctx: &Context) -> Identifier;
    // A unique name; concatenation of name and id.
    fn unique_name(&self, ctx: &Context) -> Identifier {
        match self.given_name(ctx) {
            Some(given_name) => given_name + underscore() + self.id(ctx),
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
