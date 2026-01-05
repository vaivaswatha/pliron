use crate::graph::walkers;
use crate::graph::walkers::IRNode;
use crate::graph::walkers::WALKCONFIG_PREORDER_FORWARD;
use crate::graph::walkers::interruptible::{WalkResult, walk_advance};
use crate::utils::visualize::walkers::interruptible::walk_break;
use pliron::context::Ptr;
use pliron::{
    basic_block::BasicBlock, common_traits::Named, context::Context,
    irfmt::printers::iter_with_sep, linked_list::ContainsLinkedList, op::OpObj,
    operation::Operation, printable, printable::Printable, region::Region,
};
use rustc_hash::FxHashMap;
use std::fmt::Display;
use std::ops::Deref;

pub fn visualize_operation(ctx: &Context, op: Ptr<Operation>) -> impl Display + '_ {
    Visualizer {
        graph_component: IRNode::Operation(op),
        ctx,
    }
}

pub fn visualize_basic_block(ctx: &Context, block: Ptr<BasicBlock>) -> impl Display + '_ {
    Visualizer {
        graph_component: IRNode::BasicBlock(block),
        ctx,
    }
}

pub fn visualize_region(ctx: &Context, region: Ptr<Region>) -> impl Display + '_ {
    Visualizer {
        graph_component: IRNode::Region(region),
        ctx,
    }
}

struct Visualizer<'a> {
    graph_component: IRNode,
    ctx: &'a Context,
}

impl std::fmt::Display for Visualizer<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.graph_component {
            IRNode::Operation(op) => operation_entry_point(self.ctx, *op, f),
            IRNode::BasicBlock(block) => block_entry_point(self.ctx, *block, f),
            IRNode::Region(region) => region_entry_point(self.ctx, *region, f),
        }
    }
}

// State of graphviz generation to ensure uniqueness of nodes
struct GraphState<'a, 'b> {
    op_nodes: FxHashMap<Ptr<Operation>, (u32, u32)>,
    op_counter: u32,
    f: &'a mut std::fmt::Formatter<'b>,
}

impl<'a, 'b> GraphState<'a, 'b> {
    fn new(f: &'a mut std::fmt::Formatter<'b>) -> GraphState<'a, 'b> {
        GraphState {
            op_nodes: FxHashMap::default(),
            op_counter: 0,
            f,
        }
    }

    // Retrieve index for a given [Ptr<Operation>]
    //else increment the internal counter and return a new index
    fn get_operation_index(&mut self, ptr: Ptr<Operation>) -> u32 {
        self.op_nodes
            .entry(ptr)
            .or_insert_with(|| {
                let count = self.op_counter;
                self.op_counter += 1;
                (count, 0)
            })
            .0
    }
    // Return and increment region index for a given [Ptr<Operation>] if found
    fn get_region_index(&mut self, ptr: Ptr<Operation>) -> Option<u32> {
        self.op_nodes.get_mut(&ptr).map(|(_, region_idx)| {
            let current_idx = *region_idx;
            *region_idx += 1;
            current_idx
        })
    }
}

trait ToWalkResult {
    fn to_walk_result(self) -> WalkResult<std::fmt::Error>;
}

impl ToWalkResult for std::fmt::Result {
    fn to_walk_result(self) -> WalkResult<std::fmt::Error> {
        match self {
            Ok(_) => walk_advance(),
            Err(e) => walk_break(e),
        }
    }
}

// Print basic [Operation] information
fn operation_print(ctx: &Context, op: OpObj, f: &mut std::fmt::Formatter<'_>) -> core::fmt::Result {
    let sep = printable::ListSeparator::CharSpace(',');
    let opid = op.as_ref().get_opid();
    let op = op.as_ref().get_operation().deref(ctx);
    let operands = iter_with_sep(op.operands(), sep);

    if op.get_num_results() != 0 {
        let results = iter_with_sep(op.results(), sep);
        write!(f, "{} = ", results.disp(ctx))?;
    }

    write!(f, "{} ({})", opid.disp(ctx), operands.disp(ctx))?;

    if op.get_num_successors() > 0 {
        let successors = iter_with_sep(
            op.successors()
                .map(|succ| format!("^{}", succ.unique_name(ctx))),
            sep,
        );
        write!(f, " [{}]", successors.disp(ctx))?;
    }

    Ok(())
}

fn operation_entry_point(
    ctx: &Context,
    op: Ptr<Operation>,
    f: &mut std::fmt::Formatter<'_>,
) -> core::fmt::Result {
    write!(f, "strict digraph pliron_graph {{\n rankdir=TB;\n")?;
    let graph_state = &mut GraphState::new(f);
    let _ = walkers::interruptible::immutable::walk_op(
        ctx,
        graph_state,
        &WALKCONFIG_PREORDER_FORWARD,
        op,
        graphviz_callback,
    );
    writeln!(f, "}}")?;
    Ok(())
}

fn region_entry_point(
    ctx: &Context,
    region: Ptr<Region>,
    f: &mut std::fmt::Formatter<'_>,
) -> core::fmt::Result {
    write!(f, "strict digraph pliron_graph {{\n rankdir=TB;\n")?;
    let _ = walkers::interruptible::immutable::walk_region(
        ctx,
        &mut GraphState::new(f),
        &WALKCONFIG_PREORDER_FORWARD,
        region,
        graphviz_callback,
    );
    writeln!(f, "}}")?;
    Ok(())
}

fn block_entry_point(
    ctx: &Context,
    block: Ptr<BasicBlock>,
    f: &mut std::fmt::Formatter<'_>,
) -> core::fmt::Result {
    write!(f, "strict digraph pliron_graph {{\n rankdir=TB;\n")?;
    let _ = walkers::interruptible::immutable::walk_block(
        ctx,
        &mut GraphState::new(f),
        &WALKCONFIG_PREORDER_FORWARD,
        block,
        graphviz_callback,
    );
    writeln!(f, "}}")?;
    Ok(())
}

fn graphviz_callback(
    ctx: &Context,
    graph_state: &mut GraphState,
    node: IRNode,
) -> WalkResult<std::fmt::Error> {
    match node {
        IRNode::Operation(op) => {
            let oper_index = graph_state.get_operation_index(op);
            let operation_identifier =
                if let Some(parent_block_identifier) = op.deref(ctx).get_parent_block() {
                    format!("{}", parent_block_identifier.deref(ctx).unique_name(ctx))
                } else {
                    write!(
                        graph_state.f,
                        " operation_{} [
                    shape=record,
                    style=filled, fillcolor=lightgreen, label=\"",
                        oper_index
                    )
                    .to_walk_result()?;
                    operation_print(ctx, Operation::get_op_dyn(op, ctx), graph_state.f)
                        .to_walk_result()?;
                    writeln!(graph_state.f, "\"];").to_walk_result()?;
                    format!("operation_{}", oper_index)
                };

            for region in op.deref(ctx).regions() {
                let entry_block_identifier: String = region
                    .deref(ctx)
                    .get_head()
                    .unwrap()
                    .deref(ctx)
                    .unique_name(ctx)
                    .into();
                writeln!(
                    graph_state.f,
                    "{}->{}[style = dotted];",
                    operation_identifier, entry_block_identifier
                )
                .to_walk_result()?;
            }
        }
        IRNode::BasicBlock(block) => {
            let block_identifier: String = block.deref(ctx).unique_name(ctx).into();
            write!(
                graph_state.f,
                "{} [
            shape=record,
            style=filled, fillcolor=lightgreen, label=\"",
                block_identifier
            )
            .to_walk_result()?;
            write!(graph_state.f, "{} : \\n", block_identifier).to_walk_result()?;
            for oper in block.deref(ctx).iter(ctx) {
                operation_print(ctx, Operation::get_op_dyn(oper, ctx), graph_state.f)
                    .to_walk_result()?;
                write!(graph_state.f, "\\n").to_walk_result()?;
            }
            writeln!(graph_state.f, "\"];").to_walk_result()?;
            for succ in block.deref(ctx).succs(ctx) {
                let succ_identifier: String = succ.deref(ctx).unique_name(ctx).into();
                writeln!(graph_state.f, "{}->{};", block_identifier, succ_identifier)
                    .to_walk_result()?;
            }
            if block
                == block
                    .deref(ctx)
                    .get_parent_region()
                    .unwrap()
                    .deref(ctx)
                    .get_tail()
                    .unwrap()
            {
                writeln!(graph_state.f, "}}").to_walk_result()?;
            }
        }
        IRNode::Region(region) => {
            let parent_op = region.deref(ctx).get_parent_op();
            let oper_index = graph_state.get_operation_index(parent_op);
            let region_idx = graph_state
                .get_region_index(region.deref(ctx).get_parent_op())
                .unwrap();
            let op_id = Operation::get_op_dyn(parent_op, ctx).get_opid();
            let parent_op_label = op_id.name.deref();
            write!(
                graph_state.f,
                "subgraph cluster_region_{0}_{1}{{ \n style=dotted;\n label=\"parent op : {2}, region idx : {1}\";\n",
                oper_index, region_idx, parent_op_label,
            ).to_walk_result()?;
        }
    }

    walk_advance()
}
