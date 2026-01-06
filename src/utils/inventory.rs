// This is used to print out different types for use
// with the inventory crate so that we can register
// items that have one-time dynamic initialization
// processes via LazyLock.
pub struct LazyLockWrapper<T>(pub &'static LazyLock<T>);
