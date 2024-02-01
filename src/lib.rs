//! # pliron: Programming Languages Intermediate RepresentatiON
//!
//! `pliron` is an extensible compiler IR framework, inspired by MLIR
//! and written in safe Rust.

#![forbid(unsafe_code)]

// Allow proc-macros to find this crate
extern crate self as pliron;

pub mod attribute;
pub mod basic_block;
pub mod common_traits;
pub mod context;
pub mod debug_info;
pub mod dialect;
pub mod dialects;
pub mod error;
pub mod identifier;
pub mod irfmt;
pub mod linked_list;
pub mod location;
pub mod op;
pub mod operation;
pub mod parsable;
pub mod printable;
pub mod region;
pub mod storage_uniquer;
pub mod r#type;
pub mod uniqued_any;
pub mod use_def_lists;
pub mod vec_exns;
