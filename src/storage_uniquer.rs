use rustc_hash::FxHasher;
use std::hash::{Hash, Hasher};

/// Computes the hash of a rust value and its rust type.
/// ```rust
///     use pliron::storage_uniquer::TypeValueHash;
///     #[derive(Hash)]
///     struct A { i: u64 }
///     #[derive(Hash)]
///     struct B { i: u64 }
///     let x = A { i: 10 };
///     let y = B { i: 10 };
///     assert!(TypeValueHash::new(&x) != TypeValueHash::new(&y));
/// ```
#[derive(Hash, Eq, PartialEq)]
pub struct TypeValueHash {
    hash: u64,
}

impl TypeValueHash {
    /// Hash a value and its type together.
    pub fn new<T: Hash + 'static>(t: &T) -> TypeValueHash {
        let mut hasher = FxHasher::default();
        t.hash(&mut hasher);
        std::any::TypeId::of::<T>().hash(&mut hasher);
        TypeValueHash {
            hash: hasher.finish(),
        }
    }
}
