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
use std::marker::PhantomData;
use std::ops::Deref;

pub struct Visualizer<'a> {
    graph_component: IRNode,
    ctx: &'a Context,
}

impl Display for Visualizer<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match &self.graph_component {
            IRNode::Operation(op) => wrapping_entry_point_operation(self.ctx, *op, f),
            IRNode::BasicBlock(block) => wrapping_entry_point_block(self.ctx, *block, f),
            IRNode::Region(region) => wrapping_entry_point_region(self.ctx, *region, f),
        }
    }
}

impl Visualizer<'_> {
    pub fn visualize_operation<'a>(ctx: &'a Context, op: Ptr<Operation>) -> Visualizer<'a> {
        Visualizer {
            graph_component: IRNode::Operation(op),
            ctx,
        }
    }

    pub fn visualize_basic_block<'a>(ctx: &'a Context, block: Ptr<BasicBlock>) -> Visualizer<'a> {
        Visualizer {
            graph_component: IRNode::BasicBlock(block),
            ctx,
        }
    }

    pub fn visualize_region<'a>(ctx: &'a Context, region: Ptr<Region>) -> Visualizer<'a> {
        Visualizer {
            graph_component: IRNode::Region(region),
            ctx,
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct Counter<T> {
    value: u32,
    _phantom: PhantomData<T>,
}

impl<T> Counter<T> {
    fn new() -> Self {
        Self {
            value: 0,
            _phantom: PhantomData,
        }
    }

    fn value(&self) -> u32 {
        self.value
    }

    fn increment(&mut self) {
        self.value += 1;
    }
}

// State of graphviz generation to ensure uniqueness of nodes
struct GraphState<'a, 'b> {
    op_nodes: FxHashMap<Ptr<Operation>, (u32, Counter<Region>)>,
    op_counter: Counter<Operation>,
    f: &'a mut std::fmt::Formatter<'b>,
}

impl<'a, 'b> GraphState<'a, 'b> {
    fn new(f: &'a mut std::fmt::Formatter<'b>) -> GraphState<'a, 'b> {
        GraphState {
            op_nodes: FxHashMap::default(),
            op_counter: Counter::new(),
            f,
        }
    }

    // Retrieve [Count<Operation>] for a given [Ptr<Operation>] if found
    // else increment and return
    fn get_operation_count(&mut self, ptr: Ptr<Operation>) -> u32 {
        if let Some(value) = self.op_nodes.get(&ptr) {
            value.0
        } else {
            self.op_counter.increment();
            self.op_nodes
                .insert(ptr, (self.op_counter.value(), Counter::new()));
            self.op_counter.value()
        }
    }
    // Return and increment region index for a given [Ptr<Operation>] if found
    fn get_region_index(&mut self, ptr: Ptr<Operation>) -> Option<u32> {
        if let Some((_, counter)) = self.op_nodes.get_mut(&ptr) {
            let val = counter.value();
            counter.increment();
            Some(val)
        } else {
            None
        }
    }
}

// Print basic [Operation] information
fn operation_print(ctx: &Context, op: OpObj) -> String {
    let sep = printable::ListSeparator::CharSpace(',');
    let opid = op.as_ref().get_opid();
    let op = op.as_ref().get_operation().deref(ctx);
    let operands = iter_with_sep(op.operands(), sep);

    let mut op_details = String::new();

    if op.get_num_results() != 0 {
        let results = iter_with_sep(op.results(), sep);
        op_details.push_str(&format!("{} = ", results.disp(ctx)));
    }

    op_details.push_str(&format!("{} ({})", opid.disp(ctx), operands.disp(ctx),));

    if op.successors().next().is_some() {
        let successors = iter_with_sep(
            op.successors()
                .map(|succ| format!("^{}", succ.unique_name(ctx))),
            sep,
        );
        op_details.push_str(&format!(" [{}]", successors.disp(ctx)));
    }

    op_details
}

fn wrapping_entry_point_operation(
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

fn wrapping_entry_point_region(
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

fn wrapping_entry_point_block(
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
) -> WalkResult<Result<(), std::fmt::Error>> {
    match node {
        IRNode::Operation(op) => {
            let oper_count = graph_state.get_operation_count(op);
            let operation_identifier =
                if let Some(parent_block_identifier) = op.deref(ctx).get_parent_block() {
                    format!("{}", parent_block_identifier.deref(ctx).unique_name(ctx),)
                } else {
                    if let Err(e) = write!(
                        graph_state.f,
                        " operation_{} [
                    shape=record,
                    style=filled, fillcolor=lightgreen, label=\"{}\"];",
                        oper_count,
                        operation_print(ctx, Operation::get_op_dyn(op, ctx))
                    ) {
                        return walk_break(Err(e));
                    }
                    format!("operation_{}", oper_count)
                };

            for region in op.deref(ctx).regions() {
                let entry_block_identifier: String = region
                    .deref(ctx)
                    .get_head()
                    .unwrap()
                    .deref(ctx)
                    .unique_name(ctx)
                    .into();
                if let Err(e) = writeln!(
                    graph_state.f,
                    "{}->{};",
                    operation_identifier, entry_block_identifier
                ) {
                    return walk_break(Err(e));
                }
            }
        }
        IRNode::BasicBlock(block) => {
            let block_identifier: String = block.deref(ctx).unique_name(ctx).into();
            if let Err(e) = write!(
                graph_state.f,
                "{} [
            shape=record,
            style=filled, fillcolor=lightgreen, label=\"",
                block_identifier
            ) {
                return walk_break(Err(e));
            }
            if let Err(e) = write!(graph_state.f, "{}\\n", block_identifier) {
                return walk_break(Err(e));
            }
            for oper in block.deref(ctx).iter(ctx) {
                //let op_count = graph_state.get_operation_count(oper);
                if let Err(e) = write!(
                    graph_state.f,
                    "  {}\\n",
                    operation_print(ctx, Operation::get_op_dyn(oper, ctx))
                ) {
                    return walk_break(Err(e));
                }
            }
            if let Err(e) = writeln!(graph_state.f, "\"];") {
                return walk_break(Err(e));
            }
            for succ in block.deref(ctx).succs(ctx) {
                let succ_identifier: String = succ.deref(ctx).unique_name(ctx).into();
                //let term_op_count =
                //    graph_state.get_operation_count(block.deref(ctx).get_terminator(ctx).unwrap());
                if let Err(e) =
                    writeln!(graph_state.f, "{}->{};", block_identifier, succ_identifier)
                {
                    return walk_break(Err(e));
                }
            }
            if block
                == block
                    .deref(ctx)
                    .get_parent_region()
                    .unwrap()
                    .deref(ctx)
                    .get_tail()
                    .unwrap()
                && let Err(e) = writeln!(graph_state.f, "}}")
            {
                return walk_break(Err(e));
            }
        }
        IRNode::Region(region) => {
            let oper_count = graph_state.get_operation_count(region.deref(ctx).get_parent_op());
            let region_idx = graph_state
                .get_region_index(region.deref(ctx).get_parent_op())
                .unwrap();
            let op_id = Operation::get_op_dyn(region.deref(ctx).get_parent_op(), ctx).get_opid();
            let parent_op_label = op_id.name.deref();
            if let Err(e) = write!(
                graph_state.f,
                "subgraph cluster_region_{0}_{1}{{ \n style=dotted;\n label=\"parent op : {2}, region idx - {1}\";\n",
                oper_count, region_idx, parent_op_label,
            ) {
                return walk_break(Err(e));
            }
        }
    }

    walk_advance()
}
