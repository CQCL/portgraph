use crate::{Direction, NodeIndex, PortGraph, PortIndex};
use bitvec::prelude::BitVec;
use std::{collections::VecDeque, iter::FusedIterator};

/// Iterator over a `UnweightedGraph` in topological ordering.
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
}

impl<'graph> Iterator for TopoSort<'graph> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        let Some(node) = self.candidate_nodes.pop_front() else {
            return None;
        };

        for port in self.graph.ports(node, self.direction) {
            self.remaining_ports.set(port.index(), false);

            if let Some(link) = self.graph.port_link(port) {
                self.remaining_ports.set(link.index(), false);
                let target = self.graph.port_node(link).unwrap();

                let target_ready = self
                    .graph
                    .ports(node, self.direction.reverse())
                    .all(|p| !self.remaining_ports[p.index()]);

                if target_ready {
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
