//! IR printing and parsing utilities

use crate::{parsable::Parsable, printable::Printable};

pub mod parsers;
pub mod printers;

/// An object that implements both [Printable] and [Parsable].
pub trait Format: Printable + Parsable {}
