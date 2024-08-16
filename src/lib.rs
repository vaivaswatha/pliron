//! # pliron: Programming Languages Intermediate RepresentatiON
//!
//! `pliron` is an extensible compiler IR framework, inspired by MLIR
//! and written in safe Rust.

// Allow proc-macros to find this crate
extern crate self as pliron;

pub mod attribute;
pub mod basic_block;
pub mod builtin;
pub mod common_traits;
pub mod context;
pub mod debug_info;
pub mod dialect;
pub mod graph;
pub mod identifier;
pub mod irfmt;
pub mod linked_list;
pub mod location;
pub mod op;
pub mod operation;
pub mod parsable;
pub mod printable;
pub mod region;
pub mod result;
pub mod storage_uniquer;
pub mod r#type;
pub mod uniqued_any;
pub mod utils;
pub mod value;
