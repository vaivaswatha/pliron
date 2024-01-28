//! Source location for different IR entities

use std::{fmt::Debug, path::PathBuf};

use combine::stream::position::SourcePosition;
use rustc_hash::FxHashSet;

use crate::{
    attribute::AttrObj,
    context::Context,
    irfmt::printers::list_with_sep,
    printable::{self, Printable},
    uniqued_any::{self, UniquedKey},
};

/// Where is the source program?
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum Source {
    /// Program being read from a file.
    File(UniquedKey<PathBuf>),
    /// Program is in memory.
    // TODO: Maybe have an `Rc` to the buffer?
    InMemory,
}

impl Printable for Source {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            Source::File(path_key) => {
                write!(f, "{}", uniqued_any::get(ctx, *path_key).display())
            }
            Source::InMemory => write!(f, "<in-memory>"),
        }
    }
}

/// Represents a (combination of) program source locations.
/// This captures more or less the functionality of MLIR's
/// [BuiltinLocationAttributes](https://mlir.llvm.org/docs/Dialects/Builtin/#location-attributes).
/// For simplicity, unlike in MLIR, [Location] is not extensible.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Location {
    /// A [Source] along with a [position](SourcePosition) within it.
    /// This is same as MLIR's [FileLineColLoc](https://mlir.llvm.org/docs/Dialects/Builtin/#filelinecolloc).
    SrcPos { src: Source, pos: SourcePosition },
    /// A collection of other source locations.
    /// This is same as MLIR's [FusedLoc](https://mlir.llvm.org/docs/Dialects/Builtin/#fusedloc).
    Fused {
        metadata: Option<AttrObj>,
        locations: Vec<Location>,
    },
    /// Location with a name.
    /// See [NameLoc](https://mlir.llvm.org/docs/Dialects/Builtin/#nameloc).
    Named {
        name: String,
        child_loc: Box<Location>,
    },
    /// Connects the location of a callee with the location of the caller.
    /// See [CallSiteLoc](https://mlir.llvm.org/docs/Dialects/Builtin/#callsiteloc).
    CallSite {
        callee: Box<Location>,
        caller: Box<Location>,
    },
    /// Location unknown.
    /// See [UnknownLoc](https://mlir.llvm.org/docs/Dialects/Builtin/#callsiteloc).
    Unknown,
}

impl Location {
    /// If the location is from exactly one source, get that source.
    pub fn source(&self) -> Option<Source> {
        let sources = self.sources();
        if sources.len() == 1 {
            sources.first().cloned()
        } else {
            None
        }
    }

    /// Get all sources that this location is associated with.
    pub fn sources(&self) -> Vec<Source> {
        let mut res = FxHashSet::default();
        fn sources(loc: &Location, res: &mut FxHashSet<Source>) {
            match loc {
                Location::SrcPos { src, pos: _ } => {
                    res.insert(*src);
                }
                Location::Fused {
                    metadata: _,
                    locations,
                } => {
                    for loc in locations {
                        sources(loc, res);
                    }
                }
                Location::Named { name: _, child_loc } => {
                    sources(child_loc, res);
                }
                Location::CallSite { callee, caller } => {
                    sources(callee, res);
                    sources(caller, res);
                }
                Location::Unknown => (),
            }
        }
        sources(self, &mut res);
        res.into_iter().collect()
    }
}

impl Printable for Location {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            Self::SrcPos { src, pos } => {
                write!(f, "{}: {}", src.disp(ctx), pos)
            }
            Self::Fused {
                metadata,
                locations,
            } => {
                write!(f, "fused")?;
                if let Some(metadata) = metadata {
                    write!(f, "<{}>", metadata.disp(ctx))?;
                }
                write!(
                    f,
                    "[{}]",
                    list_with_sep(locations, printable::ListSeparator::CharSpace(',')).disp(ctx),
                )
            }
            Self::Named { name, child_loc } => {
                write!(f, "{}({})", name, child_loc.disp(ctx))
            }
            Self::CallSite { callee, caller } => {
                write!(f, "callsite({} at {})", callee.disp(ctx), caller.disp(ctx))
            }
            Self::Unknown => write!(f, "?"),
        }
    }
}

/// Any object that has an associated location.
pub trait Located {
    fn loc(&self) -> Location;
    fn set_loc(&mut self, loc: Location);
}
