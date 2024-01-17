//! Utility traits such as [Named], [Verify] etc.

use crate::{
    context::{private::ArenaObj, Context, Ptr},
    error::Result,
};

/// IR entities that have a qualified name within a dialect.
/// All Attribute and Type instances are qualified objects with their <kind>ID type as the
/// qualifier.
pub trait Qualified {
    type Qualifier;

    fn get_qualifier(&self, ctx: &Context) -> Self::Qualifier;
}

impl<T: Qualified> Qualified for &T {
    type Qualifier = T::Qualifier;

    fn get_qualifier(&self, ctx: &Context) -> Self::Qualifier {
        (*self).get_qualifier(ctx)
    }
}

impl<T: Qualified + ?Sized> Qualified for Box<T> {
    type Qualifier = T::Qualifier;

    fn get_qualifier(&self, ctx: &Context) -> Self::Qualifier {
        (**self).get_qualifier(ctx)
    }
}

impl<T: Qualified + ArenaObj> Qualified for Ptr<T> {
    type Qualifier = T::Qualifier;

    fn get_qualifier(&self, ctx: &Context) -> Self::Qualifier {
        self.deref(ctx).get_qualifier(ctx)
    }
}

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
