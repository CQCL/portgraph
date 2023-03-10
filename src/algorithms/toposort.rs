use crate::{Direction, NodeIndex, PortGraph, PortIndex};
use bitvec::prelude::BitVec;
use std::{collections::VecDeque, iter::FusedIterator};

/// Returns an iterator over a [`Portgraph`] in topological ordering.
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
    TopoSort::new(graph, source, direction)
}

/// Iterator over a [`Portgraph`] in topological ordering.
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
}

impl<'graph> TopoSort<'graph> {
    /// Initialises a new topological sort of a portgraph in a specified direction
    /// starting at a collection of `source` nodes.
    pub fn new(
        graph: &'graph PortGraph,
        source: impl IntoIterator<Item = NodeIndex>,
        direction: Direction,
    ) -> Self {
        let mut remaining_ports = BitVec::with_capacity(graph.port_capacity());
        remaining_ports.resize(graph.port_capacity(), true);

        Self {
            graph,
            remaining_ports,
            candidate_nodes: source.into_iter().collect(),
            direction,
            nodes_seen: 0,
        }
    }

    /// Returns whether there are ports that have not been visited yet.
    /// If the iterator has seen all nodes this implies that there is a cycle.
    pub fn ports_remaining(&self) -> impl ExactSizeIterator<Item = PortIndex> + '_ {
        self.remaining_ports.iter_ones().map(PortIndex::new)
    }

    /// Checks if a node is ready to be visited, i.e. it has been reached from
    /// all its linked ports.
    fn target_ready(&mut self, node: NodeIndex) -> bool {
        self.graph.ports(node, self.direction.reverse()).all(|p| {
            if !self.remaining_ports[p.index()] {
                true
            } else if self.graph.port_link(p).is_none() {
                // If the port is not linked, mark it as visited.
                self.remaining_ports.set(p.index(), false);
                true
            } else {
                false
            }
        })
    }
}

impl<'graph> Iterator for TopoSort<'graph> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.candidate_nodes.pop_front()?;

        for port in self.graph.ports(node, self.direction) {
            self.remaining_ports.set(port.index(), false);

            if let Some(link) = self.graph.port_link(port) {
                self.remaining_ports.set(link.index(), false);
                let target = self.graph.port_node(link).unwrap();

                if self.target_ready(target) {
                    self.candidate_nodes.push_back(target);
                }
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
    use crate::{algorithms::toposort, Direction, PortGraph};

    #[test]
    fn small_toposort() {
        let mut graph = PortGraph::new();
        let node_a = graph.add_node(2, 3);
        let node_b = graph.add_node(3, 2);

        // Add two edges between node A and B
        graph.link_nodes(node_a, 0, node_b, 0).unwrap();
        graph.link_nodes(node_a, 1, node_b, 1).unwrap();

        // Run a topological sort on the graph starting at node A.
        let topo = toposort(&graph, [node_a], Direction::Outgoing);
        assert_eq!(topo.collect::<Vec<_>>(), [node_a, node_b]);
    }
}
