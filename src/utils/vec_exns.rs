//! Extend functionality of Rust vectors.

/// This trait provides additionaly functionality for Rust vectors
pub trait VecExtns<T> {
    /// Insert a new element and get back its index in the container.
    fn push_back(&mut self, t: T) -> usize;
    /// Insert a new element, constructed by calling `ctor`,
    /// and get back its index in the container. `ctor` will
    /// receve the index as a parameter. This is useful when the
    /// element inserted needs to know its index.
    fn push_back_with(&mut self, ctor: impl FnMut(usize) -> T) -> usize;

    /// Create and initialize a new vector.
    fn new_init<U: FnMut(usize) -> T>(size: usize, initf: U) -> Vec<T>;
}

impl<T> VecExtns<T> for Vec<T> {
    fn push_back(&mut self, t: T) -> usize {
        self.push(t);
        self.len() - 1
    }

    fn push_back_with(&mut self, mut ctor: impl FnMut(usize) -> T) -> usize {
        let idx = self.len();
        self.push(ctor(idx));
        idx
    }

    fn new_init<U: FnMut(usize) -> T>(size: usize, mut initf: U) -> Vec<T> {
        let mut v = Vec::<T>::with_capacity(size);
        for i in 0..size {
            v.push(initf(i));
        }
        v
    }
}
