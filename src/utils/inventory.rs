//! Helpers for integration for inventory
use std::marker::PhantomData;
use std::sync::LazyLock;

/// This is used to print out different types for use
/// with the inventory crate so that we can register
/// items that have one-time dynamic initialization
/// processes via LazyLock. The U parameter is for
/// further distinguishing in cases where T is similar.
pub struct LazyLockWrapper<T: 'static, U = ()>(
    pub &'static LazyLock<T>,
    pub PhantomData<U>,
);

impl<T, U> LazyLockWrapper<T, U> {
    pub const fn new(t: &'static LazyLock<T>) -> Self {
        Self(t, PhantomData)
    }
}
