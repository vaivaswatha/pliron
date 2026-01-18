// We use these instead of std::collection::HashMap
// because they provide lower-level APIs which are
// handy for performance-sensitive parts of the code.
pub type FxHashMap<K, V> = hashbrown::HashMap<K, V, rustc_hash::FxBuildHasher>;
pub type FxHashSet<T> = hashbrown::HashSet<T, rustc_hash::FxBuildHasher>;

pub use hashbrown::hash_map::Entry;
pub use hashbrown::hash_map::RawEntryMut;
pub use rustc_hash::FxHasher;
