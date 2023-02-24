use super::post_order::PostOrder;
use crate::{secondary::SecondaryMap, Direction, NodeIndex, PortGraph};
use std::cmp::Ordering;

pub struct DominatorTree {
    root: NodeIndex,
    idom: SecondaryMap<NodeIndex, Option<NodeIndex>>,
}

impl DominatorTree {
    pub fn new(graph: &PortGraph, entry: NodeIndex, direction: Direction) -> Self {
        // We traverse the graph in post order starting at the `entry` node.
        // We associate each node that we encounter with its index within the traversal.
        let mut node_to_index = SecondaryMap::with_capacity(graph.node_capacity());
        let mut index_to_node = Vec::with_capacity(graph.node_capacity());

        for (index, node) in PostOrder::new(graph, [entry], direction).enumerate() {
            node_to_index[node] = index;
            index_to_node.push(node);
        }

        // We keep track of node's immediate dominators by their post order index.
        // We set the entry node (i.e. the last node in the post oder traversal) it to dominate itself.
        let num_nodes = index_to_node.len();
        let mut dominators = vec![usize::MAX; num_nodes];
        *dominators.last_mut().unwrap() = num_nodes - 1;

        // Iterate until we have reached a fixed point
        let mut changed = true;
        while changed {
            changed = false;

            for post_order_index in (0..num_nodes - 1).rev() {
                let node = index_to_node[post_order_index];

                // PERFORMANCE: Here we look up the node's predecessors every time;
                // instead we could create an array which holds the predecessor post order indices
                // in sequence. But given that there won't be many iterations of this at all,
                // that is probably too costly.
                let new_dominator = graph
                    .ports(node, direction.reverse())
                    .flat_map(|port| graph.port_link(port))
                    .flat_map(|link| graph.port_node(link))
                    .map(|pred| node_to_index[pred])
                    .filter(|pred_index| dominators[*pred_index] != usize::MAX)
                    .reduce(|index1, index2| intersect(&dominators, index1, index2))
                    .expect("there must be at least one predecessor with known dominator");

                if new_dominator != dominators[post_order_index] {
                    changed = true;
                    dominators[post_order_index] = new_dominator;
                }
            }
        }

        // Translate into a secondary map with `NodeIndex`s.
        let mut idom = SecondaryMap::with_capacity(graph.node_capacity());

        for (index, dominator) in dominators.into_iter().take(num_nodes - 1).enumerate() {
            debug_assert_ne!(dominator, usize::MAX);
            idom[index_to_node[index]] = Some(index_to_node[dominator]);
        }

        Self { root: entry, idom }
    }

    #[inline]
    pub fn root(&self) -> NodeIndex {
        self.root
    }

    #[inline]
    pub fn immediate_dominator(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.idom[node]
    }
}

#[inline]
fn intersect(dominators: &[usize], mut finger1: usize, mut finger2: usize) -> usize {
    loop {
        match finger1.cmp(&finger2) {
            Ordering::Less => finger1 = dominators[finger1],
            Ordering::Equal => return finger1,
            Ordering::Greater => finger2 = dominators[finger2],
        }
    }
}
