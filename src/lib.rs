//! # pliron: Programming Languages Intermediate RepresentatiON
//!
//! `pliron` is an extensible compiler IR framework, inspired by MLIR
//! and written in safe Rust.

// Allow proc-macros to find this crate
extern crate self as pliron;

// Export pliron_derive as pliron::derive for procedural macros.
pub use pliron_derive as derive;

// Export linkme as pliron::linkme for procedural macros.
// This re-export is tricky, and we use the workaround here:
// https://github.com/dtolnay/linkme/issues/108#issuecomment-3308031385
#[cfg(not(target_family = "wasm"))]
pub use linkme;
// Export combine as pliron::combine for procedural macros.
pub use combine;
// Export dyn_clone as pliron::dyn_clone for procedural macros.
pub use dyn_clone;
// Export inventory as pliron::inventory for procedural macros.
#[cfg(target_family = "wasm")]
pub use inventory;

pub mod attribute;
pub mod basic_block;
pub mod builtin;
pub mod common_traits;
pub mod context;
pub mod debug_info;
pub mod dialect;
pub mod graph;
pub mod identifier;
pub mod inserter;
pub mod irfmt;
pub mod linked_list;
pub mod location;
pub mod op;
pub mod operation;
pub mod parsable;
pub mod printable;
pub mod region;
pub mod result;
pub mod rewriter;
pub mod storage_uniquer;
pub mod symbol_table;
pub mod r#type;
pub mod uniqued_any;
pub mod utils;
pub mod value;
