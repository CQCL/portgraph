use super::postorder;
use crate::{secondary::SecondaryMap, Direction, NodeIndex, PortGraph};
use std::cmp::Ordering;

/// Returns a dominator tree for a [`PortGraph`], where each node is dominated
/// by its parent.
///
/// # Example
///
/// The following example runs the dominator algorithm on the following branching graph:
///    ┏> b ┓
/// a ─┫    ┣─> c ─> e
///    ┗> d ┛
///
/// ```
/// # use portgraph::{algorithms::dominators, Direction, PortGraph};
/// let mut graph = PortGraph::with_capacity(5, 10);
/// let a = graph.add_node(0,2);
/// let b = graph.add_node(1,1);
/// let c = graph.add_node(2,1);
/// let d = graph.add_node(1,1);
/// let e = graph.add_node(1,0);
///
/// graph.link_nodes(a, 0, b, 0).unwrap();
/// graph.link_nodes(a, 1, d, 0).unwrap();
/// graph.link_nodes(b, 0, c, 0).unwrap();
/// graph.link_nodes(d, 0, c, 1).unwrap();
/// graph.link_nodes(c, 0, e, 0).unwrap();
///
/// let tree = dominators(&graph, a, Direction::Outgoing);
/// assert_eq!(tree.root(), a);
/// assert_eq!(tree.immediate_dominator(a), None);
/// assert_eq!(tree.immediate_dominator(b), Some(a));
/// assert_eq!(tree.immediate_dominator(c), Some(a));
/// assert_eq!(tree.immediate_dominator(d), Some(a));
/// assert_eq!(tree.immediate_dominator(e), Some(c));
/// ```
pub fn dominators(graph: &PortGraph, entry: NodeIndex, direction: Direction) -> DominatorTree {
    DominatorTree::new(graph, entry, direction)
}

/// A dominator tree for a [`PortGraph`].
///
/// See [`dominators`] for more information.
pub struct DominatorTree {
    root: NodeIndex,
    /// The immediate dominator of each node.
    idom: SecondaryMap<NodeIndex, Option<NodeIndex>>,
}

impl DominatorTree {
    fn new(graph: &PortGraph, entry: NodeIndex, direction: Direction) -> Self {
        // We traverse the graph in post order starting at the `entry` node.
        // We associate each node that we encounter with its index within the traversal.
        let mut node_to_index = SecondaryMap::with_capacity(graph.node_capacity());
        let mut index_to_node = Vec::with_capacity(graph.node_capacity());

        for (index, node) in postorder(graph, [entry], direction).enumerate() {
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
    /// Returns the root of the dominator tree.
    pub fn root(&self) -> NodeIndex {
        self.root
    }

    #[inline]
    /// Returns the immediate dominator of a node.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dominators_small() {
        //     ┏> b ┓
        //  a ─┫    ┣─> c ─> e
        //     ┗> d ┛
        let mut graph = PortGraph::with_capacity(5, 10);
        let a = graph.add_node(0, 2);
        let b = graph.add_node(1, 1);
        let c = graph.add_node(2, 1);
        let d = graph.add_node(1, 1);
        let e = graph.add_node(1, 0);

        graph.link_nodes(a, 0, b, 0).unwrap();
        graph.link_nodes(a, 1, d, 0).unwrap();
        graph.link_nodes(b, 0, c, 0).unwrap();
        graph.link_nodes(d, 0, c, 1).unwrap();
        graph.link_nodes(c, 0, e, 0).unwrap();

        // From `a`
        let tree = dominators(&graph, a, Direction::Outgoing);
        assert_eq!(tree.root(), a);
        assert_eq!(tree.immediate_dominator(a), None);
        assert_eq!(tree.immediate_dominator(b), Some(a));
        assert_eq!(tree.immediate_dominator(c), Some(a));
        assert_eq!(tree.immediate_dominator(d), Some(a));
        assert_eq!(tree.immediate_dominator(e), Some(c));

        // Backwards from `c`
        let tree = dominators(&graph, c, Direction::Incoming);
        assert_eq!(tree.root(), c);
        assert_eq!(tree.immediate_dominator(a), Some(c));
        assert_eq!(tree.immediate_dominator(b), Some(c));
        assert_eq!(tree.immediate_dominator(c), None);
        assert_eq!(tree.immediate_dominator(d), Some(c));
        assert_eq!(tree.immediate_dominator(e), None);
    }

    #[test]
    fn test_dominators_complex() {
        // This graph is taken from the paper "A Simple, Fast Dominance Algorithm"
        // by Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy.
        // Figure 4, page 8.
        let mut graph = PortGraph::with_capacity(6, 18);
        let entry = graph.add_node(0, 2);
        let a = graph.add_node(1, 1);
        let b = graph.add_node(1, 2);
        let c = graph.add_node(2, 1);
        let d = graph.add_node(3, 2);
        let e = graph.add_node(2, 1);

        graph.link_nodes(entry, 0, a, 0).unwrap();
        graph.link_nodes(entry, 1, b, 0).unwrap();
        graph.link_nodes(a, 0, c, 0).unwrap();
        graph.link_nodes(b, 0, d, 0).unwrap();
        graph.link_nodes(b, 1, e, 0).unwrap();
        graph.link_nodes(c, 0, d, 1).unwrap();
        graph.link_nodes(d, 0, c, 1).unwrap();
        graph.link_nodes(d, 1, e, 1).unwrap();
        graph.link_nodes(e, 0, d, 2).unwrap();

        let dominators = dominators(&graph, entry, Direction::Outgoing);

        assert_eq!(dominators.root(), entry);
        assert_eq!(dominators.immediate_dominator(entry), None);
        assert_eq!(dominators.immediate_dominator(a), Some(entry));
        assert_eq!(dominators.immediate_dominator(b), Some(entry));
        assert_eq!(dominators.immediate_dominator(c), Some(entry));
        assert_eq!(dominators.immediate_dominator(d), Some(entry));
        assert_eq!(dominators.immediate_dominator(e), Some(entry));
    }
}
