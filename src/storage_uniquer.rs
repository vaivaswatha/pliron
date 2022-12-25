//! Store unique instances of a rust type.
//! Only a single unique copy (in self context) will
//! exit of objects instantiated by this utility.

use rustc_hash::{FxHashMap, FxHasher};
use std::{
    cell::RefCell,
    collections::hash_map::Entry,
    hash::{Hash, Hasher},
};

use crate::context::{ArenaCell, ArenaIndex};

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

/// Hash the (to be) unique object.
pub type UniqueStoreHash<T> = fn(&T) -> TypeValueHash;

/// Are the two objects equal.
pub type UniqueStoreEq<T> = fn(t1: &T, t2: &T) -> bool;

/// Is the provided argument equal to the unique object under interest.
pub type UniqueStoreIs<'a, T> = &'a dyn Fn(&T) -> bool;

/// Store unique copy of objects.
pub struct UniqueStore<T: 'static> {
    pub unique_store: ArenaCell<T>,
    pub unique_stores_map: FxHashMap<TypeValueHash, Vec<ArenaIndex>>,
}

impl<T: 'static> Default for UniqueStore<T> {
    fn default() -> Self {
        Self {
            unique_store: Default::default(),
            unique_stores_map: Default::default(),
        }
    }
}

impl<T: 'static> UniqueStore<T> {
    /// Get or create a unique copy of `t: T`.
    /// Consumes the provided argument either way.
    /// Returns [generational_arena::Index] into [UniqueStore::unique_store] of the unique copy.
    pub fn get_or_create_unique(
        &mut self,
        t: T,
        hash: UniqueStoreHash<T>,
        eq: UniqueStoreEq<T>,
    ) -> ArenaIndex {
        let hash = hash(&t);
        match self.unique_stores_map.entry(hash) {
            Entry::Occupied(mut possible_matches) => {
                let index = possible_matches.get().iter().find_map(|index| {
                    let iref = &*self.unique_store.get(*index).unwrap().borrow_mut();
                    if eq(&t, iref) {
                        Some(*index)
                    } else {
                        None
                    }
                });
                let index = index.unwrap_or(self.unique_store.insert(RefCell::new(t)));
                possible_matches.get_mut().push(index);
                index
            }
            Entry::Vacant(slot) => {
                let new_index = self.unique_store.insert(RefCell::new(t));
                slot.insert(vec![new_index]);
                new_index
            }
        }
    }

    /// Get index to the stored object that satisfies `hash` and `is`.
    pub fn get(&self, hash: TypeValueHash, is: UniqueStoreIs<T>) -> Option<ArenaIndex> {
        self.unique_stores_map
            .get(&hash)
            .and_then(|mv| {
                mv.iter()
                    .find(|other| is(&*self.unique_store.get(**other).unwrap().borrow()))
            })
            .copied()
    }
}
