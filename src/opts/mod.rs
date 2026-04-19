//! Optimizations

use std::ops::{BitOr, BitOrAssign};

pub mod mem2reg;

/// Indicates whether an optimization pass changed the IR or not.
/// Implements `|` and `|=` for convenience.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OptStatus {
    #[default]
    IRUnchanged,
    IRChanged,
}

impl BitOr for OptStatus {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (OptStatus::IRUnchanged, OptStatus::IRUnchanged) => OptStatus::IRUnchanged,
            _ => OptStatus::IRChanged,
        }
    }
}

impl BitOrAssign for OptStatus {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}
