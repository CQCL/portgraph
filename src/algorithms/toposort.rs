use crate::{Direction, NodeIndex, PortGraph, PortIndex};
use bitvec::prelude::BitVec;
use std::{collections::VecDeque, iter::FusedIterator};

/// Returns an iterator over a [`PortGraph`] in topological order.
///
/// Optimized for full graph traversal, i.e. when all nodes are reachable from the source nodes.
/// It uses O(n) memory, where n is the number of ports in the graph.
///
/// Implements [Kahn's algorithm](https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm).
///
/// # Example
///
/// ```
/// # use portgraph::{algorithms::toposort, Direction, PortGraph};
/// let mut graph = PortGraph::new();
/// let node_a = graph.add_node(2, 2);
/// let node_b = graph.add_node(2, 2);
/// graph.link_nodes(node_a, 0, node_b, 0).unwrap();
///
/// // Run a topological sort on the graph starting at node A.
/// let topo = toposort(&graph, [node_a], Direction::Outgoing);
/// assert_eq!(topo.collect::<Vec<_>>(), [node_a, node_b]);
/// ```
pub fn toposort(
    graph: &PortGraph,
    source: impl IntoIterator<Item = NodeIndex>,
    direction: Direction,
) -> TopoSort {
    TopoSort::new(graph, source, direction, None, None)
}

/// Returns an iterator over a [`PortGraph`] in topological order, filtering the
/// nodes and ports to consider.
///
/// If the filter closures return false for a node or port, it is skipped.
///
/// Optimized for full graph traversal, i.e. when all nodes are reachable from the source nodes.
/// It uses O(n) memory, where n is the number of ports in the graph.
///
/// Implements [Kahn's
/// algorithm](https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm).
///
/// # Example
///
/// ```
/// # use portgraph::{Direction, PortGraph};
/// # use portgraph::algorithms::{toposort, toposort_filtered};
/// let mut graph = PortGraph::new();
/// let node_a = graph.add_node(2, 2);
/// let node_b = graph.add_node(2, 2);
/// let node_c = graph.add_node(2, 2);
/// let node_d = graph.add_node(2, 2);
/// graph.link_nodes(node_a, 0, node_b, 0).unwrap();
/// graph.link_nodes(node_a, 1, node_c, 0).unwrap();
///
/// // Run a topological sort on the graph starting at node A.
/// let topo = toposort_filtered(
///     &graph,
///     [node_a, node_d],
///     Direction::Outgoing,
///     |n| n != node_d,
///     |p| Some(p) != graph.output(node_a, 1),
/// );
/// assert_eq!(topo.collect::<Vec<_>>(), [node_a, node_b]);
/// ```
pub fn toposort_filtered<'graph>(
    graph: &'graph PortGraph,
    source: impl IntoIterator<Item = NodeIndex>,
    direction: Direction,
    node_filter: impl FnMut(NodeIndex) -> bool + 'graph,
    port_filter: impl FnMut(PortIndex) -> bool + 'graph,
) -> TopoSort {
    TopoSort::new(
        graph,
        source,
        direction,
        Some(Box::new(node_filter)),
        Some(Box::new(port_filter)),
    )
}

/// Iterator over a [`PortGraph`] in topological order.
///
/// See [`toposort`] for more information.
///
/// Implements [Kahn's algorithm](https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm).
pub struct TopoSort<'graph> {
    graph: &'graph PortGraph,
    remaining_ports: BitVec,
    /// A VecDeque is used for the node list to produce a canonical ordering,
    /// as successors of nodes already have a canonical ordering due to ports.
    candidate_nodes: VecDeque<NodeIndex>,
    direction: Direction,
    /// The number of nodes already returned from the iterator.
    /// This is used to calculate the upper bound for the iterator's `size_hint`.
    nodes_seen: usize,
    /// A filter closure for the nodes to visit. If the closure returns false,
    /// the node is skipped.
    node_filter: Option<Box<dyn FnMut(NodeIndex) -> bool + 'graph>>,
    /// A filter closure for the ports to visit. If the closure returns false,
    /// the port is skipped.
    port_filter: Option<Box<dyn FnMut(PortIndex) -> bool + 'graph>>,
}

impl<'graph> TopoSort<'graph> {
    /// Initialises a new topological sort of a portgraph in a specified direction
    /// starting at a collection of `source` nodes.
    fn new(
        graph: &'graph PortGraph,
        source: impl IntoIterator<Item = NodeIndex>,
        direction: Direction,
        mut node_filter: Option<Box<dyn FnMut(NodeIndex) -> bool + 'graph>>,
        port_filter: Option<Box<dyn FnMut(PortIndex) -> bool + 'graph>>,
    ) -> Self {
        let mut remaining_ports = BitVec::with_capacity(graph.port_capacity());
        remaining_ports.resize(graph.port_capacity(), true);

        let candidate_nodes: VecDeque<_> = if let Some(node_filter) = node_filter.as_mut() {
            source.into_iter().filter(|&n| node_filter(n)).collect()
        } else {
            source.into_iter().collect()
        };

        // Mark all the candidate ports as visited, so we don't visit them again.
        for node in candidate_nodes.iter() {
            for port in graph.ports(*node, direction.reverse()) {
                remaining_ports.set(port.index(), false);
            }
        }

        Self {
            graph,
            remaining_ports,
            candidate_nodes,
            direction,
            nodes_seen: 0,
            node_filter,
            port_filter,
        }
    }

    /// Returns whether there are ports that have not been visited yet.
    /// If the iterator has seen all nodes this implies that there is a cycle.
    pub fn ports_remaining(&self) -> impl ExactSizeIterator<Item = PortIndex> + '_ {
        self.remaining_ports.iter_ones().map(PortIndex::new)
    }

    /// Checks if a node becomes ready once it is visited from `from_port`, i.e.
    /// it has been reached from all its linked ports.
    fn becomes_ready(&mut self, node: NodeIndex, from_port: PortIndex) -> bool {
        if self.ignore_node(node) {
            return false;
        }
        self.graph.ports(node, self.direction.reverse()).all(|p| {
            if p == from_port {
                // This port must have not been visited yet. Otherwise, the node
                // would have been already been reported as ready and added to
                // the candidate list.
                self.remaining_ports[p.index()]
            } else if !self.remaining_ports[p.index()] {
                true
            } else if self.graph.port_link(p).is_none() || self.ignore_port(p) {
                // If the port is not linked or should be ignored, mark it as visited.
                self.remaining_ports.set(p.index(), false);
                true
            } else {
                false
            }
        })
    }

    /// Returns `true` if the node should be ignored.
    #[inline]
    fn ignore_node(&mut self, node: NodeIndex) -> bool {
        !self
            .node_filter
            .as_mut()
            .map_or(true, |filter| filter(node))
    }

    /// Returns `true` if the port should be ignored.
    #[inline]
    fn ignore_port(&mut self, port: PortIndex) -> bool {
        !self
            .port_filter
            .as_mut()
            .map_or(true, |filter| filter(port))
    }
}

impl<'graph> Iterator for TopoSort<'graph> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.candidate_nodes.pop_front()?;

        for port in self.graph.ports(node, self.direction) {
            self.remaining_ports.set(port.index(), false);

            if self.ignore_port(port) {
                continue;
            }

            if let Some(link) = self.graph.port_link(port) {
                let target = self.graph.port_node(link).unwrap();

                if self.becomes_ready(target, link) {
                    self.candidate_nodes.push_back(target);
                }
                self.remaining_ports.set(link.index(), false);
            }
        }

        self.nodes_seen += 1;
        Some(node)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (
            self.candidate_nodes.len(),
            Some(self.graph.node_count() - self.nodes_seen),
        )
    }
}

impl<'graph> FusedIterator for TopoSort<'graph> {}

#[cfg(test)]
mod test {
    use super::*;

    use crate::{Direction, PortGraph};

    #[test]
    fn small_toposort() {
        let mut graph = PortGraph::new();
        let node_a = graph.add_node(2, 3);
        let node_b = graph.add_node(3, 2);
        let node_c = graph.add_node(3, 2);
        let node_d = graph.add_node(3, 2);

        // Add two edges between node A and B
        graph.link_nodes(node_a, 0, node_b, 0).unwrap();
        graph.link_nodes(node_a, 1, node_b, 1).unwrap();
        graph.link_nodes(node_b, 0, node_c, 0).unwrap();
        graph.link_nodes(node_c, 0, node_d, 0).unwrap();

        // Run a topological sort on the graph starting at node A.
        let topo = toposort(&graph, [node_a, node_d], Direction::Outgoing);
        assert_eq!(topo.collect::<Vec<_>>(), [node_a, node_d, node_b, node_c]);

        let topo_filtered = toposort_filtered(
            &graph,
            [node_a, node_d],
            Direction::Outgoing,
            |n| n != node_d,
            |p| Some(p) != graph.output(node_b, 0),
        );
        assert_eq!(topo_filtered.collect::<Vec<_>>(), [node_a, node_b]);
    }
}
