use rustc_hash::FxHashMap;

use crate::{
    basic_block::BasicBlock, context::{Context, Ptr}, graph::{traversals}, linked_list::{ContainsLinkedList}, region::Region
};
/// A node in the dominator tree.
pub struct DomTreeNode {
    /// The immediate dominator of self.
    pub parent: Option<Ptr<BasicBlock>>,
    /// The blocks that self immediately dominates.
    pub children: Vec<Ptr<BasicBlock>>,
}

#[derive(Default)]
pub struct DomTree(FxHashMap<Ptr<BasicBlock>, DomTreeNode>);

/// Computes a dominator tree from each of `region`'s basic block to its immediate dominator
pub fn compute_dominator_tree(region: &Region, ctx: &Context) -> DomTree {
    // An implementation of the algorithm from page 7 of "A Simple, Fast Dominance Algorithm" by Cooper et. al.

    if region.get_head() == None {
        return DomTree(FxHashMap::default())
    };

    let rpo = traversals::region::topological_order(ctx, region.self_ptr);
    let rpo_index: FxHashMap<Ptr<BasicBlock>, usize> = rpo.iter()
        .enumerate()
        .map(|(i, &block)| (block, i))
        .collect();

    let mut dom : Vec<Option<usize>> = vec![None; rpo.len()];
    dom[0] = Some(0);

    fn intersect(a: usize, b: usize, dom: &[Option<usize>]) -> usize {
        if a == b { return a };
        if a > b { return intersect(dom[a].unwrap(),b,&dom) };
        return intersect(a, dom[b].unwrap(), &dom);
    }

    loop {
        let mut changed = false;

        for (i, &block) in rpo.iter().enumerate().skip(1) {
            let mut new_dom = None;
            // only consider predecessors reachable from entry (i.e. those in rpo_index)
            for pred in block.preds(ctx).iter().filter(|p| rpo_index.contains_key(&p)) {
                let pred_idx = rpo_index[&pred];
                match (dom[pred_idx], new_dom) {
                    (None, _) => {},
                    (Some(n), None) => { new_dom = Some(n) },
                    (Some(n), Some(m)) => { new_dom = Some(intersect(n,m, &dom)); }
                }
            }
            if dom[i] != new_dom {
                dom[i] = new_dom;
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    let mut dom_tree = DomTree::default();
    let entry = DomTreeNode { parent: None, children: vec![] };
    dom_tree.0.insert(rpo[0], entry);

    let child_parent = dom.iter()
        .enumerate()
        .skip(1)
        .map(|(i,parent)| (rpo[i], rpo[parent.unwrap()]));

    for (child_block,parent_block) in child_parent {
        let child_node = DomTreeNode { parent: Some(parent_block), children: vec![] };
        dom_tree.0.insert(child_block, child_node);
        let parent_node = dom_tree.0.get_mut(&parent_block).unwrap();
        parent_node.children.push(child_block)
    }

    dom_tree
}
