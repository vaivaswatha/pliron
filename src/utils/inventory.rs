//! Helpers for integration for inventory

use std::sync::LazyLock;

/// A wrapper around [LazyLock] to allow its use with [inventory](crate::inventory).
/// "This collect! call must be in the same crate that defines the plugin type."
pub struct LazyLockWrapper<T: 'static>(pub &'static LazyLock<T>);
