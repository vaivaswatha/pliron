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
    graph_component: &'a dyn Graphviz,
    ctx: &'a Context,
}

impl Display for Visualizer<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.graph_component.wrapping_entry_point(self.ctx, f)
    }
}

impl Visualizer<'_> {
    pub fn visualise_operation<'a>(
        ctx: &'a Context,
        operation: &'a Ptr<Operation>,
    ) -> Visualizer<'a> {
        Visualizer {
            graph_component: operation,
            ctx,
        }
    }

    pub fn visualise_basic_block<'a>(
        ctx: &'a Context,
        block: &'a Ptr<BasicBlock>,
    ) -> Visualizer<'a> {
        Visualizer {
            graph_component: block,
            ctx,
        }
    }

    pub fn visualise_region<'a>(ctx: &'a Context, region: &'a Ptr<Region>) -> Visualizer<'a> {
        Visualizer {
            graph_component: region,
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
struct GraphState {
    op_nodes: FxHashMap<Ptr<Operation>, (u32, Counter<Region>)>,
    op_counter: Counter<Operation>,
}

impl GraphState {
    fn new() -> GraphState {
        GraphState {
            op_nodes: FxHashMap::default(),
            op_counter: Counter::new(),
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
    let successors = iter_with_sep(
        op.successors()
            .map(|succ| "^".to_string() + &succ.unique_name(ctx)),
        sep,
    );
    format!(
        "{} ({}) [{}]",
        opid.disp(ctx),
        operands.disp(ctx),
        successors.disp(ctx),
    )
}
trait Graphviz {
    fn wrapping_entry_point(
        &self,
        ctx: &Context,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "strict digraph pliron_graph {{\n rankdir=LR;\n")?;
        self.create_graph(ctx, &mut GraphState::new(), f)?;
        write!(f, "}}\n")?;
        Ok(())
    }
    fn create_graph(
        &self,
        ctx: &Context,
        graph_state: &mut GraphState,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result;
}

impl Graphviz for Ptr<Operation> {
    fn create_graph(
        &self,
        ctx: &Context,
        graph_state: &mut GraphState,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        let oper_count = graph_state.get_operation_count(*self);
        write!(
            f,
            "operation_{} [style=filled, label=\"{}\",shape=rectangle, fillcolor=\"#7ef97eff\"];\n",
            oper_count,
            operation_print(ctx, Operation::get_op_dyn(*self, ctx)),
        )?;

        for region in self.deref(ctx).regions() {
            region.create_graph(ctx, graph_state, f)?;
            let entry_block_identifier: String = region
                .deref(ctx)
                .get_head()
                .unwrap()
                .deref(ctx)
                .unique_name(ctx)
                .into();
            write!(f, "operation_{}->{};\n", oper_count, entry_block_identifier)?;
        }
        Ok(())
    }
}

impl Graphviz for Ptr<BasicBlock> {
    fn create_graph(
        &self,
        ctx: &Context,
        graph_state: &mut GraphState,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        let block_identifier: String = self.deref(ctx).unique_name(ctx).into();
        write!(
            f,
            "subgraph cluster_{} {{ \n style=invis;\n rank=same;\n",
            block_identifier
        )?;
        write!(
            f,
            "{} [style =filled, shape=ellipse, fillcolor=\"#bb30b6ff\"];\n",
            block_identifier
        )?;
        write!(f, "{}", block_identifier)?;
        for oper in self.deref(ctx).iter(ctx) {
            write!(f, "->operation_{}", graph_state.get_operation_count(oper),).unwrap();
        }
        write!(f, "[weight=100,style=invis];\n")?;
        for oper in self.deref(ctx).iter(ctx) {
            oper.create_graph(ctx, graph_state, f)?;
        }
        write!(f, "}}\n")?;
        for succ in self.deref(ctx).succs(ctx) {
            let succ_identifier: String = succ.deref(ctx).unique_name(ctx).into();
            write!(f, "{}->{};\n", block_identifier, succ_identifier)?;
        }
        Ok(())
    }
}

impl Graphviz for Ptr<Region> {
    fn create_graph(
        &self,
        ctx: &Context,
        graph_state: &mut GraphState,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(
            f,
            "subgraph cluster_region_{0}_{1}{{ \n style=dotted;\n label=\"parent op : {2}, region idx - {1}\";\n",
            graph_state.get_operation_count(self.deref(ctx).get_parent_op()),
            graph_state
                .get_region_index(self.deref(ctx).get_parent_op())
                .unwrap(),
            Operation::get_op_dyn(self.deref(ctx).get_parent_op(), ctx)
                .get_opid()
                .name
                .deref(),
        )?;
        for block in self.deref(ctx).iter(ctx) {
            block.create_graph(ctx, graph_state, f)?;
        }
        write!(f, "}}\n")?;
        Ok(())
    }
}
