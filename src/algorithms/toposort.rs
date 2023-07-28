use crate::{Direction, LinkView, NodeIndex, PortIndex, SecondaryMap};
use bitvec::prelude::BitVec;
use std::{collections::VecDeque, fmt::Debug, iter::FusedIterator};

/// Returns an iterator over a [`LinkView`] in topological order.
///
/// The `Map` type parameter specifies the type of the secondary map that is
/// used to store the dominator tree data. The default is [`BitVec`], which is
/// efficient for full graph traversal, i.e. when all nodes are reachable from
/// the source nodes. For sparse traversals, `HashMap` or `BTreeMap` may be more
/// efficient.
///
/// Implements [Kahn's algorithm](https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm).
///
/// # Example
///
/// ```
/// # use ::portgraph::algorithms::*;
/// # use ::portgraph::*;
/// let mut graph = PortGraph::new();
/// let node_a = graph.add_node(2, 2);
/// let node_b = graph.add_node(2, 2);
/// graph.link_nodes(node_a, 0, node_b, 0).unwrap();
///
/// // Run a topological sort on the graph starting at node A.
/// let topo: TopoSort<_> = toposort(&graph, [node_a], Direction::Outgoing);
/// assert_eq!(topo.collect::<Vec<_>>(), [node_a, node_b]);
/// ```
pub fn toposort<'f, Map, G: LinkView>(
    graph: G,
    source: impl IntoIterator<Item = NodeIndex>,
    direction: Direction,
) -> TopoSort<'f, G, Map>
where
    Map: SecondaryMap<PortIndex, bool>,
{
    TopoSort::new(graph, source, direction, None, None)
}

/// Returns an iterator over a [`LinkView`] in topological order, applying a
/// filter to the nodes and ports. No filtered nodes are returned, and neither
/// are any nodes only accessible via filtered nodes or filtered ports.
///
/// If the filter closures return false for a node or port, it is skipped.
///
/// The `Map` type parameter specifies the type of the secondary map that is
/// used to store the dominator tree data. The default is [`BitVec`], which is
/// efficient for full graph traversal, i.e. when all nodes are reachable from
/// the source nodes. For sparse traversals, `HashMap` or `BTreeMap` may be more
/// efficient.
///
/// Implements [Kahn's
/// algorithm](https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm).
///
/// # Example
///
/// ```
/// # use ::portgraph::algorithms::*;
/// # use ::portgraph::*;
/// let mut graph = PortGraph::new();
/// let node_a = graph.add_node(2, 2);
/// let node_b = graph.add_node(2, 2);
/// let node_c = graph.add_node(2, 2);
/// let node_d = graph.add_node(2, 2);
/// graph.link_nodes(node_a, 0, node_b, 0).unwrap();
/// graph.link_nodes(node_a, 1, node_c, 0).unwrap();
///
/// // Run a topological sort on the graph starting at node A.
/// let topo: TopoSort<_> = toposort_filtered(
///     &graph,
///     [node_a, node_d],
///     Direction::Outgoing,
///     |n| n != node_d,
///     |_, p| Some(p) != graph.output(node_a, 1),
/// );
/// assert_eq!(topo.collect::<Vec<_>>(), [node_a, node_b]);
/// ```
pub fn toposort_filtered<'f, Map, G>(
    graph: G,
    source: impl IntoIterator<Item = NodeIndex>,
    direction: Direction,
    node_filter: impl FnMut(NodeIndex) -> bool + 'f,
    port_filter: impl FnMut(NodeIndex, PortIndex) -> bool + 'f,
) -> TopoSort<'f, G, Map>
where
    Map: SecondaryMap<PortIndex, bool>,
    G: LinkView,
{
    TopoSort::new(
        graph,
        source,
        direction,
        Some(Box::new(node_filter)),
        Some(Box::new(port_filter)),
    )
}

/// Iterator over a [`LinkView`] in topological order.
///
/// See [`toposort`] for more information.
///
/// Implements [Kahn's algorithm](https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm).
pub struct TopoSort<'f, G, Map = BitVec> {
    graph: G,
    visited_ports: Map,
    /// A VecDeque is used for the node list to produce a canonical ordering,
    /// as successors of nodes already have a canonical ordering due to ports.
    candidate_nodes: VecDeque<NodeIndex>,
    direction: Direction,
    /// The number of nodes already returned from the iterator.
    /// This is used to calculate the upper bound for the iterator's `size_hint`.
    nodes_seen: usize,
    /// A filter closure for the nodes to visit. If the closure returns false,
    /// the node is skipped.
    node_filter: Option<Box<dyn FnMut(NodeIndex) -> bool + 'f>>,
    /// A filter closure for the ports to visit. If the closure returns false,
    /// the port is skipped.
    port_filter: Option<Box<dyn FnMut(NodeIndex, PortIndex) -> bool + 'f>>,
}

impl<'f, Map, G> TopoSort<'f, G, Map>
where
    Map: SecondaryMap<PortIndex, bool>,
    G: LinkView,
{
    /// Initialises a new topological sort of a portgraph in a specified direction
    /// starting at a collection of `source` nodes.
    ///
    /// If the default value of `Map` is not `false`, this requires O(#ports) time.
    fn new(
        graph: G,
        source: impl IntoIterator<Item = NodeIndex>,
        direction: Direction,
        mut node_filter: Option<Box<dyn FnMut(NodeIndex) -> bool + 'f>>,
        port_filter: Option<Box<dyn FnMut(NodeIndex, PortIndex) -> bool + 'f>>,
    ) -> Self {
        let mut visited_ports: Map = SecondaryMap::new();

        let candidate_nodes: VecDeque<_> = if let Some(node_filter) = node_filter.as_mut() {
            source.into_iter().filter(|&n| node_filter(n)).collect()
        } else {
            source.into_iter().collect()
        };

        // If the default value of `Map` is not `false`, we must mark all ports as not visited.
        if visited_ports.default_value() {
            for port in graph.ports_iter() {
                visited_ports.set(port, false);
            }
        }

        // Mark all the candidate ports as visited, so we don't visit them again.
        for node in candidate_nodes.iter() {
            for port in graph.ports(*node, direction.reverse()) {
                visited_ports.set(port, true);
            }
        }

        Self {
            graph,
            visited_ports,
            candidate_nodes,
            direction,
            nodes_seen: 0,
            node_filter,
            port_filter,
        }
    }

    /// Returns whether there are ports that have not been visited yet.
    /// If the iterator has seen all nodes this implies that there is a cycle.
    // pub fn ports_remaining(&self) -> impl DoubleEndedIterator<Item = PortIndex> + '_ {
    pub fn ports_remaining(&self) -> impl Iterator<Item = PortIndex> + '_ {
        self.graph
            .ports_iter()
            .filter(move |&p| !self.visited_ports.get(p))
    }

    /// Checks if a node becomes ready once it is visited from `from_port`, i.e.
    /// it has been reached from all its linked ports.
    fn becomes_ready(&mut self, node: NodeIndex, from_port: impl Into<PortIndex>) -> bool {
        let from_port = from_port.into();
        if self.ignore_node(node) {
            return false;
        }
        let ports: Vec<_> = self.graph.ports(node, self.direction.reverse()).collect();
        ports.into_iter().all(|p| {
            if p == from_port {
                // This port must have not been visited yet. Otherwise, the node
                // would have been already been reported as ready and added to
                // the candidate list.
                !self.visited_ports.get(p)
            } else if *self.visited_ports.get(p) {
                true
            } else if self.graph.port_link(p).is_none() || self.ignore_port(node, p) {
                // If the port is not linked or should be ignored, mark it as visited.
                self.visited_ports.set(p, true);
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
    fn ignore_port(&mut self, node: NodeIndex, port: PortIndex) -> bool {
        !self
            .port_filter
            .as_mut()
            .map_or(true, |filter| filter(node, port))
    }
}

impl<'f, Map, G> Iterator for TopoSort<'f, G, Map>
where
    Map: SecondaryMap<PortIndex, bool>,
    G: LinkView,
{
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.candidate_nodes.pop_front()?;
        let ports = self.graph.ports(node, self.direction).collect::<Vec<_>>();

        for port in ports {
            self.visited_ports.set(port, true);

            if self.ignore_port(node, port) {
                continue;
            }

            if let Some(link) = self.graph.port_link(port) {
                let target = self.graph.port_node(link).unwrap();

                if self.becomes_ready(target, link) {
                    self.candidate_nodes.push_back(target);
                }
                self.visited_ports.set(link.into(), true);
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

impl<'f, Map, G> FusedIterator for TopoSort<'f, G, Map>
where
    Map: SecondaryMap<PortIndex, bool>,
    G: LinkView,
{
}

impl<'f, Map, G> Debug for TopoSort<'f, G, Map>
where
    Map: Debug,
    G: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TopoSort")
            .field("graph", &self.graph)
            .field("visited_ports", &self.visited_ports)
            .field("candidate_nodes", &self.candidate_nodes)
            .field("direction", &self.direction)
            .field("nodes_seen", &self.nodes_seen)
            .finish()
    }
}
#[cfg(test)]
mod test {
    use super::*;

    use crate::{Direction, LinkMut, PortGraph, PortMut, PortView};

    #[test]
    fn small_toposort() {
        let mut graph = PortGraph::new();
        let node_a = graph.add_node(2, 3);
        let node_b = graph.add_node(3, 2);
        let node_c = graph.add_node(3, 2);
        let node_d = graph.add_node(3, 2);
        let node_e = graph.add_node(3, 2);

        // Add two edges between node A and B
        graph.link_nodes(node_a, 0, node_b, 0).unwrap();
        graph.link_nodes(node_a, 1, node_b, 1).unwrap();
        graph.link_nodes(node_a, 2, node_e, 0).unwrap();
        graph.link_nodes(node_b, 0, node_c, 0).unwrap();
        graph.link_nodes(node_c, 0, node_d, 0).unwrap();

        // Run a topological sort on the graph starting at node A.
        let topo: TopoSort<_> = toposort(&graph, [node_a, node_d], Direction::Outgoing);
        assert_eq!(
            topo.collect::<Vec<_>>(),
            [node_a, node_d, node_b, node_e, node_c]
        );

        let topo_filtered: TopoSort<_> = toposort_filtered(
            &graph,
            [node_a, node_d],
            Direction::Outgoing,
            |n| ![node_d, node_e].contains(&n),
            |_, p| Some(p) != graph.output(node_b, 0),
        );
        assert_eq!(topo_filtered.collect::<Vec<_>>(), [node_a, node_b]);
    }
}
