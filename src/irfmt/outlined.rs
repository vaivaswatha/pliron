//! Printer and parser for outlined attributes.
//! Outlined attributes are printed in a separate section of the
//! IR, after the top level operation is printed.

use combine::{Parser, between, optional, parser::char::spaces, token};
use rustc_hash::FxHashMap;

use crate::{
    attribute::{AttrObj, attr_impls},
    builtin::attr_interfaces::{OutlinedAttr, PrintOnceAttr},
    context::{Context, Ptr},
    dict_key,
    identifier::Identifier,
    input_err, input_error,
    location::{Located, Location},
    operation::Operation,
    parsable::{Parsable, StateStream},
    printable::{self, Printable},
    result::Result,
    utils::vec_exns::VecExtns,
};

use super::parsers::{delimited_list_parser, location, spaced, zero_or_more_parser};

#[derive(Default)]
struct OutlinePrintState {
    /// Operations that have some outline item to be printed
    outlined_ops: Vec<Ptr<Operation>>,
    /// [PrintOnceAttr]s, mapped to their outindex.
    print_once_attrs: FxHashMap<AttrObj, usize>,
}

dict_key!(OUTLINED_STATE, "outlined_state");

/// An [Operation] was just printed, and we now print a future reference to the
/// outlined attributes (if any) or location (if any) that will be printed later.
pub(crate) fn preprint_outline(
    ctx: &Context,
    opr: Ptr<Operation>,
    print_state: printable::State,
    f: &mut core::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let mut aux_print_data = print_state.aux_data_mut();
    let print_state = aux_print_data
        .entry(OUTLINED_STATE.clone())
        .or_insert(Box::new(OutlinePrintState::default()))
        .downcast_mut::<OutlinePrintState>()
        .expect("failed to downcast outline print state");

    let op = opr.deref(ctx);

    // If it has a location, we need to outline the location.
    if !op.loc().is_unknown() {
        let outindex = print_state.outlined_ops.push_back(opr);
        return write!(f, " !{outindex}");
    }

    // Check if there's any attribute that's outlined.
    if op
        .attributes
        .0
        .iter()
        .any(|(_, attr)| attr_impls::<dyn OutlinedAttr>(&**attr))
    {
        let outindex = print_state.outlined_ops.push_back(opr);
        return write!(f, " !{outindex}");
    }

    Ok(())
}

/// Print the outlined attributes and locations.
/// This is called after all operations have been printed.
pub(crate) fn print_outlines(
    ctx: &Context,
    print_state: printable::State,
    f: &mut core::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let Some(print_state) = print_state.aux_data_mut().remove(&OUTLINED_STATE) else {
        return Ok(());
    };

    let mut print_state = *print_state
        .downcast::<OutlinePrintState>()
        .expect("failed to downcast outline print state");

    if print_state.outlined_ops.is_empty() {
        return Ok(());
    }

    writeln!(f, "\n\noutlined_attributes:")?;
    let mut print_once_attr_indices = print_state.outlined_ops.len();
    for (outidx, op) in print_state.outlined_ops.iter().enumerate() {
        let loc = op.deref(ctx).loc();
        write!(f, "!{outidx} = ")?;
        if !loc.is_unknown() {
            write!(f, "@[{}], ", loc.disp(ctx))?;
        }
        write!(f, "[")?;
        let mut first = true;
        for (attr_name, attr) in op.deref(ctx).attributes.0.iter() {
            if attr_impls::<dyn OutlinedAttr>(&**attr) {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;
                if attr_impls::<dyn PrintOnceAttr>(&**attr) {
                    if let Some(outindex) = print_state.print_once_attrs.get(attr) {
                        write!(f, "{attr_name} = !{outindex}")?;
                    } else {
                        // If this is the first time we see this PrintOnceAttr,
                        // we need to store it for later.
                        print_state
                            .print_once_attrs
                            .insert(attr.clone(), print_once_attr_indices);
                        write!(f, "{attr_name} = !{print_once_attr_indices}")?;
                        print_once_attr_indices += 1;
                    }
                } else {
                    write!(f, "{} = {}", attr_name, attr.disp(ctx))?;
                }
            }
        }
        writeln!(f, "]")?;
    }

    // Now print the PrintOnceAttrs, if any.
    if !print_state.print_once_attrs.is_empty() {
        for (attr, outindex) in print_state.print_once_attrs {
            writeln!(f, "!{} = {}", outindex, attr.disp(ctx))?;
        }
    }

    Ok(())
}

/// The state used to parse outlined attributes and locations.
#[derive(Default)]
struct OutlineParseState {
    /// Map an outline item number to the [Operation] it refers to.
    outindex_map: FxHashMap<usize, Ptr<Operation>>,
}

/// Each [Operation] is associated with an optional [Location] and
/// a number of outlined attributes or references to them.
enum AttrOrOutlineEntryRef {
    Attr(AttrObj),
    /// The location here is where the entry ref (`!<outindex>`) is,
    /// mainly for reporting errors.
    OutlineEntryRef((Location, usize)),
}

enum OutlineEntry {
    /// A [PrintOnceAttr] is an entry by itself.
    PrintOnceAttr(AttrObj),
    /// The outline entry for an [Operation].
    OperationData(Option<Location>, Vec<(Identifier, AttrOrOutlineEntryRef)>),
}

/// An [Operation] was just parsed, see if it has any outlined item number and note that down.
pub(crate) fn postparse_outline(state_stream: &mut StateStream, op: Ptr<Operation>) -> Result<()> {
    let mut outindex_parser = spaces().with(optional(combine::token('!').with(usize::parser(()))));

    let loc = state_stream.loc();
    let outindex = match outindex_parser.parse_stream(state_stream).into_result() {
        Ok((Some(outindex), _)) => outindex,
        Ok((None, _)) => {
            // No outline index, nothing to do.
            return Ok(());
        }
        Err(e) => {
            return input_err!(
                loc,
                "Error parsing outline index for operation: {}",
                e.into_inner().error
            );
        }
    };

    let parse_state = state_stream
        .state
        .aux_data
        .entry(OUTLINED_STATE.clone())
        .or_insert(Box::new(OutlineParseState::default()))
        .downcast_mut::<OutlineParseState>()
        .expect("failed to downcast outline parse state");

    match parse_state.outindex_map.entry(outindex) {
        std::collections::hash_map::Entry::Occupied(_) => {
            return input_err!(loc, "Duplicate outline index: {}", outindex);
        }
        std::collections::hash_map::Entry::Vacant(entry) => {
            entry.insert(op);
        }
    }

    Ok(())
}

/// Parse the outlined attributes and locations.
pub(crate) fn parse_outlines(state_stream: &mut StateStream) -> Result<()> {
    let Some(parse_state) = state_stream.state.aux_data.remove(&OUTLINED_STATE) else {
        return Ok(());
    };

    let mut parse_state = *parse_state
        .downcast::<OutlineParseState>()
        .expect("failed to downcast outline parse state");

    if parse_state.outindex_map.is_empty() {
        return Ok(());
    }

    let outindex_parser = || (location(), token('!').with(usize::parser(())));

    // We'll first try to parse `OutlineEntry::OperationData`
    let optional_loc_parser = optional(
        token('@')
            .with(between(
                token('['),
                token(']'),
                spaced(Location::parser(())),
            ))
            .skip(spaced(token(','))),
    );
    let name_attr_parser = (
        Identifier::parser(()).skip(spaced(token('='))),
        AttrObj::parser(())
            .map(AttrOrOutlineEntryRef::Attr)
            .or(outindex_parser().map(AttrOrOutlineEntryRef::OutlineEntryRef)),
    );
    let name_attrs_parser = delimited_list_parser('[', ']', ',', name_attr_parser);
    let operation_data_parser = (
        spaces().with(optional_loc_parser),
        spaces().with(name_attrs_parser),
    )
        .map(|(loc, name_attrs)| OutlineEntry::OperationData(loc, name_attrs));

    let print_once_attr_parser = AttrObj::parser(()).map(OutlineEntry::PrintOnceAttr);

    let outline_entry_parser = (
        outindex_parser().skip(spaced(token('='))),
        operation_data_parser.or(print_once_attr_parser),
    );

    let start_loc = state_stream.loc();
    let (mut entries, _): (Vec<((Location, usize), OutlineEntry)>, _) =
        spaced(combine::parser::char::string("outlined_attributes:"))
            .with(zero_or_more_parser(outline_entry_parser))
            .parse_stream(state_stream)
            .into_result()
            .map_err(|e| {
                let e = e.into_inner().error;
                let loc = if let Some(src) = start_loc.source() {
                    // There's a source, use it to create a more precise location.
                    Location::SrcPos {
                        src,
                        pos: e.position,
                    }
                } else {
                    // No source, use the start location.
                    start_loc
                };
                input_error!(loc, "Error parsing outline entries: {}", e)
            })?;

    // Separate the two kinds of entries we have.
    let print_once_entries: FxHashMap<_, _> = entries
        .extract_if(0..entries.len(), |e| {
            matches!(e.1, OutlineEntry::PrintOnceAttr(_))
        })
        .map(|(outindex, entry)| {
            if let OutlineEntry::PrintOnceAttr(attr) = entry {
                (outindex.1, attr)
            } else {
                unreachable!("print_once_entries should only contain PrintOnceAttr entries")
            }
        })
        .collect();

    let operation_data_entries = entries
        .into_iter()
        .map(|(outindex, entry)| {
            let OutlineEntry::OperationData(loc, attrs) = entry else {
                unreachable!("operation_data_entries should only contain OperationData entries");
            };
            (outindex, (loc, attrs))
        })
        .collect::<Vec<_>>();

    for ((outindex_loc, outindex), (loc_opt, named_attrs)) in operation_data_entries {
        let opr = match parse_state.outindex_map.remove(&outindex) {
            Some(opr) => opr,
            None => {
                return input_err!(
                    outindex_loc,
                    "No operation found for outline index: {}",
                    outindex
                );
            }
        };

        if let Some(loc) = loc_opt {
            opr.deref_mut(state_stream.state.ctx).set_loc(loc);
        }
        for (name, attr_or_ref) in named_attrs {
            match attr_or_ref {
                AttrOrOutlineEntryRef::Attr(attr) => {
                    opr.deref_mut(state_stream.state.ctx)
                        .attributes
                        .0
                        .insert(name, attr);
                }
                AttrOrOutlineEntryRef::OutlineEntryRef((ref_outindex_loc, ref_outindex)) => {
                    if let Some(attr) = print_once_entries.get(&ref_outindex) {
                        opr.deref_mut(state_stream.state.ctx)
                            .attributes
                            .0
                            .insert(name, attr.clone());
                    } else {
                        return input_err!(
                            ref_outindex_loc,
                            "No PrintOnceAttr found for outline index: {}",
                            ref_outindex
                        );
                    }
                }
            }
        }
    }

    Ok(())
}
