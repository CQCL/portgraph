//! Convexity checking for portgraphs.
//!
//! This is based on a [`ConvexChecker`] object that is expensive to create
//! (linear in the size of the graph), but can be reused to check multiple
//! subgraphs for convexity quickly.

use std::collections::BTreeSet;

use crate::algorithms::toposort;
use crate::{Direction, LinkView, NodeIndex, PortIndex, SecondaryMap, UnmanagedDenseMap};

use super::TopoSort;

/// A pre-computed data structure for fast convexity checking.
pub struct ConvexChecker<G> {
    graph: G,
    // The nodes in topological order.
    topsort_nodes: Vec<NodeIndex>,
    // The index of a node in the topological order (the inverse of topsort_nodes).
    topsort_ind: UnmanagedDenseMap<NodeIndex, usize>,
    // The layer of each node in `topsort_nodes`.
    //
    // Layer 0 contains the end nodes of the DAG (nodes without output
    // neighbours). Layer `n` contains nodes where all output neighbours are in
    // lower layers, and at least one is in layer `n-1`.
    layer_from_end: Vec<usize>,
}

impl<G> ConvexChecker<G>
where
    G: LinkView + Clone,
{
    /// Create a new ConvexChecker.
    #[inline]
    pub fn new(graph: G) -> Self {
        let inputs = graph
            .nodes_iter()
            .filter(|&n| graph.input_neighbours(n).count() == 0);
        let topsort: TopoSort<_> = toposort(graph.clone(), inputs, Direction::Outgoing);
        let topsort_nodes: Vec<_> = topsort.collect();
        let mut topsort_ind = UnmanagedDenseMap::with_capacity(graph.node_count());
        let mut layer_from_end = vec![usize::MAX; graph.node_count()];
        for (i, &n) in topsort_nodes.iter().enumerate().rev() {
            topsort_ind.set(n, i);
            // Compute the layer of each node.
            // Since we are traversing the graph in reverse topological order, this is a simple bfs.
            layer_from_end[i] = graph
                .output_neighbours(n)
                .map(|neigh| layer_from_end[topsort_ind[neigh]] + 1)
                .max()
                .unwrap_or(0);
        }
        Self {
            graph,
            topsort_nodes,
            topsort_ind,
            layer_from_end,
        }
    }

    /// The graph on which convexity queries can be made.
    #[inline]
    pub fn graph(&self) -> G {
        self.graph.clone()
    }

    /// Whether the subgraph induced by the node set is convex.
    ///
    /// An induced subgraph is convex if there is no node that is both in the
    /// past and in the future of another node of the subgraph.
    ///
    /// This function requires mutable access to `self` because it uses a
    /// temporary data structure within the object.
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
        if nodes.is_empty() {
            return true;
        }

        // The range of considered nodes, as positions in the toposorted vector.
        // Since the nodes are ordered, any node outside of this range will
        // necessarily be outside the convex hull.
        let min_ind = *nodes.first().unwrap();
        let max_ind = *nodes.last().unwrap();
        let node_range = min_ind..=max_ind;

        // Nodes that can break the convexity must also be in the range of layers.
        let (min_layer, max_layer) =
            nodes
                .iter()
                .fold((usize::MAX, usize::MIN), |(min, max), &n| {
                    let layer = self.layer_from_end[n];
                    (min.min(layer), max.max(layer))
                });
        let layer_range = min_layer..=max_layer;

        let node_filter =
            |n| node_range.contains(&n) && layer_range.contains(&self.layer_from_end[n]);

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
                    .filter(|&n| node_filter(n))
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
                    .filter(|&n| node_filter(n))
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

    /// Whether a subgraph is convex.
    ///
    /// A subgraph is convex if there is no path between two nodes of the
    /// subgraph that has an edge outside of the subgraph.
    ///
    /// Equivalently, we check the following two conditions:
    ///  - There is no node that is both in the past and in the future of
    ///    another node of the subgraph (convexity on induced subgraph),
    ///  - There is no edge from an output port to an input port.
    ///
    /// This function requires mutable access to `self` because it uses a
    /// temporary data structure within the object.
    ///
    /// ## Arguments
    ///
    /// - `nodes`: The nodes of the subgraph of `self.graph`,
    /// - `inputs`: The input ports of the subgraph of `self.graph`. These must
    ///   be [`Direction::Incoming`] ports of a node in `nodes`,
    /// - `outputs`: The output ports of the subgraph of `self.graph`. These
    ///   must be [`Direction::Outgoing`] ports of a node in `nodes`.
    ///
    /// Any edge between two nodes of the subgraph that does not have an explicit
    /// input or output port is considered within the subgraph.
    #[inline]
    pub fn is_convex(
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

#[cfg(test)]
mod tests {
    use crate::{LinkMut, NodeIndex, PortGraph, PortMut, PortView};

    use super::ConvexChecker;

    fn graph() -> (PortGraph, [NodeIndex; 7]) {
        let mut g = PortGraph::new();
        let i1 = g.add_node(0, 2);
        let i2 = g.add_node(0, 1);
        let i3 = g.add_node(0, 1);

        let n1 = g.add_node(2, 2);
        g.link_nodes(i1, 0, n1, 0).unwrap();
        g.link_nodes(i2, 0, n1, 1).unwrap();

        let n2 = g.add_node(2, 2);
        g.link_nodes(i1, 1, n2, 0).unwrap();
        g.link_nodes(i3, 0, n2, 1).unwrap();

        let o1 = g.add_node(2, 0);
        g.link_nodes(n1, 0, o1, 0).unwrap();
        g.link_nodes(n2, 0, o1, 1).unwrap();

        let o2 = g.add_node(2, 0);
        g.link_nodes(n1, 1, o2, 0).unwrap();
        g.link_nodes(n2, 1, o2, 1).unwrap();

        (g, [i1, i2, i3, n1, n2, o1, o2])
    }

    #[test]
    fn induced_convexity_test() {
        let (g, [i1, i2, i3, n1, n2, o1, o2]) = graph();
        let checker = ConvexChecker::new(&g);

        assert!(checker.is_node_convex([i1, i2, i3]));
        assert!(checker.is_node_convex([i1, n2]));
        assert!(!checker.is_node_convex([i1, n2, o2]));
        assert!(!checker.is_node_convex([i1, n2, o1]));
        assert!(checker.is_node_convex([i1, n2, o1, n1]));
        assert!(checker.is_node_convex([i1, n2, o2, n1]));
        assert!(checker.is_node_convex([i1, i3, n2]));
        assert!(!checker.is_node_convex([i1, i3, o2]));
    }

    #[test]
    fn edge_convexity_test() {
        let (g, [i1, i2, _, n1, n2, _, o2]) = graph();
        let checker = ConvexChecker::new(&g);

        assert!(checker.is_convex(
            [i1, n2],
            [g.input(n2, 1).unwrap()],
            [
                g.output(i1, 0).unwrap(),
                g.output(n2, 0).unwrap(),
                g.output(n2, 1).unwrap()
            ]
        ));

        assert!(checker.is_convex(
            [i2, n1, o2],
            [g.input(n1, 0).unwrap(), g.input(o2, 1).unwrap()],
            [g.output(n1, 0).unwrap(),]
        ));

        assert!(!checker.is_convex(
            [i2, n1, o2],
            [
                g.input(n1, 0).unwrap(),
                g.input(o2, 1).unwrap(),
                g.input(o2, 0).unwrap()
            ],
            [g.output(n1, 0).unwrap(), g.output(n1, 1).unwrap()]
        ));
    }

    #[test]
    fn dangling_input() {
        let mut g = PortGraph::new();
        let n = g.add_node(1, 1);
        let checker = ConvexChecker::new(&g);
        assert!(checker.is_node_convex([n]));
    }

    #[test]
    fn disconnected_graph() {
        let mut g = PortGraph::new();
        let n = g.add_node(1, 1);
        g.add_node(1, 1);
        let checker = ConvexChecker::new(&g);
        assert!(checker.is_node_convex([n]));
    }
}
