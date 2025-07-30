use std::collections::BTreeSet;

use crate::algorithms::{toposort, TopoSort};
use crate::{Direction, LinkView, NodeIndex, PortIndex, SecondaryMap, UnmanagedDenseMap};

use super::{ConvexChecker, CreateConvexChecker};

/// Convexity checking using a pre-computed topological node order.
pub struct TopoConvexChecker<G> {
    graph: G,
    // The nodes in topological order
    topsort_nodes: Vec<NodeIndex>,
    // The index of a node in the topological order (the inverse of topsort_nodes)
    topsort_ind: UnmanagedDenseMap<NodeIndex, usize>,
}

impl<G: LinkView> TopoConvexChecker<G> {
    /// Create a new ConvexChecker.
    pub fn new(graph: G) -> Self {
        let inputs = graph
            .nodes_iter()
            .filter(|&n| graph.input_neighbours(n).count() == 0);
        let topsort: TopoSort<_> = toposort(&graph, inputs, Direction::Outgoing);
        let topsort_nodes: Vec<_> = topsort.collect();
        let mut topsort_ind = UnmanagedDenseMap::with_capacity(graph.node_count());
        for (i, &n) in topsort_nodes.iter().enumerate() {
            topsort_ind.set(n, i);
        }
        Self {
            graph,
            topsort_nodes,
            topsort_ind,
        }
    }

    /// The graph on which convexity queries can be made.
    #[deprecated(note = "will return a reference to the graph in the future")]
    pub fn graph(&self) -> G
    where
        G: Clone,
    {
        self.graph.clone()
    }

    /// Whether the subgraph induced by the node set is convex.
    ///
    /// An induced subgraph is convex if there is no node that is both in the
    /// past and in the future of some nodes in the subgraph.
    ///
    /// ## Arguments
    ///
    /// - `nodes`: The nodes inducing a subgraph of `self.graph()`.
    ///
    /// ## Algorithm
    ///
    /// Each node in the "vicinity" of the subgraph will be assigned a causal
    /// property, either of being in the past or in the future of the subgraph.
    /// It can then be checked whether there is a node in the past that is also
    /// in the future, violating convexity.
    ///
    /// Currently, the "vicinity" of a subgraph is defined as the set of nodes
    /// that are in the interval between the first and last node of the subgraph
    /// in some topological order. In the worst case this will traverse every
    /// node in the graph and can be improved on in the future.
    pub fn is_node_convex(&self, nodes: impl IntoIterator<Item = NodeIndex>) -> bool {
        // The nodes in the subgraph, in topological order.
        let nodes: BTreeSet<_> = nodes.into_iter().map(|n| self.topsort_ind[n]).collect();
        if nodes.len() <= 1 {
            return true;
        }

        // The range of considered nodes, as positions in the toposorted vector.
        // Since the nodes are ordered, any node outside of this range will
        // necessarily be outside the convex hull.
        let min_ind = *nodes.first().unwrap();
        let max_ind = *nodes.last().unwrap();
        let node_range = min_ind..=max_ind;

        let mut node_iter = nodes.iter().copied().peekable();

        // Nodes in the causal future of `nodes` (inside `node_range`).
        let mut other_nodes = BTreeSet::new();

        loop {
            if node_iter.peek().is_none() {
                break;
            }
            if other_nodes.is_empty() || node_iter.peek() < other_nodes.first() {
                let current = node_iter.next().unwrap();
                let current_node = self.topsort_nodes[current];
                for neighbour in self
                    .graph
                    .output_neighbours(current_node)
                    .map(|n| self.topsort_ind[n])
                    .filter(|ind| node_range.contains(ind))
                {
                    if !nodes.contains(&neighbour) {
                        other_nodes.insert(neighbour);
                    }
                }
            } else {
                let current = other_nodes.pop_first().unwrap();
                let current_node = self.topsort_nodes[current];
                for neighbour in self
                    .graph
                    .output_neighbours(current_node)
                    .map(|n| self.topsort_ind[n])
                    .filter(|ind| node_range.contains(ind))
                {
                    if nodes.contains(&neighbour) {
                        // A non-subgraph node in the causal future of the subgraph has an output neighbour in the subgraph.
                        return false;
                    } else {
                        other_nodes.insert(neighbour);
                    }
                }
            }
        }
        true
    }
}

impl<G: LinkView> ConvexChecker for TopoConvexChecker<G> {
    fn is_convex(
        &self,
        nodes: impl IntoIterator<Item = NodeIndex>,
        inputs: impl IntoIterator<Item = PortIndex>,
        outputs: impl IntoIterator<Item = PortIndex>,
    ) -> bool {
        let pre_outputs: BTreeSet<_> = outputs
            .into_iter()
            .filter_map(|p| Some(self.graph.port_link(p)?.into()))
            .collect();
        if inputs.into_iter().any(|p| pre_outputs.contains(&p)) {
            return false;
        }
        self.is_node_convex(nodes)
    }
}

impl<G: LinkView> CreateConvexChecker<G> for TopoConvexChecker<G> {
    fn new_convex_checker(graph: G) -> Self {
        Self::new(graph)
    }

    fn graph(&self) -> &G {
        &self.graph
    }
}
