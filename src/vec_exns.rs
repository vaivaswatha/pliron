//! Extend functionality of Rust vectors.

pub trait VecExtns<T> {
    // Insert a new element and get back its index in the container.
    fn push_back(&mut self, t: T) -> usize;
    // Create and initialize a new vector.
    fn new_init<U: FnMut(usize) -> T>(size: usize, initf: U) -> Vec<T>;
}

impl<T> VecExtns<T> for Vec<T> {
    fn push_back(&mut self, t: T) -> usize {
        self.push(t);
        self.len() - 1
    }

    fn new_init<U: FnMut(usize) -> T>(size: usize, mut initf: U) -> Vec<T> {
        let mut v = Vec::<T>::with_capacity(size);
        for i in 0..size {
            v.push(initf(i));
        }
        v
    }
}
