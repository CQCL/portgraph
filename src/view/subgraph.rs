//! Views into non-hierarchical parts of `PortView`s.

use std::borrow::Cow;
use std::collections::{BTreeSet, HashMap};

use delegate::delegate;
use itertools::{Either, Itertools};

use crate::boundary::{Boundary, HasBoundary};
use crate::{
    algorithms::{ConvexChecker, TopoConvexChecker},
    Direction, LinkView, NodeIndex, PortIndex,
};
use crate::{LinkError, PortOffset};

use super::{LinkMut, MultiView, PortView};

/// View into a subgraph of a PortView.
///
/// The subgraph is given by boundary edges that define where one "enters" the
/// subgraph (incoming boundary edge) and one "leaves" it (outgoing boundary
/// edges).
///
/// A subgraph is well-defined if the incoming/outgoing boundary edges partition
/// the edges between the children of the root node into three sets:
///  - boundary edges: either incoming boundary or outgoing boundary edges,
///  - interior edges: edges such that all the successor edges are either
///    outgoing boundary edges or interior edges AND all the predecessor edges
///    are either incoming boundary edges or interior edges,
///  - exterior edges: edges such that all the successor edges are either
///    incoming boundary edges or exterior edges AND all the predecessor edges
///    are either outgoing boundary edges or exterior edges.
///
/// Then the subgraph is made of the interior edges and contains all nodes that
/// are
///  - adjacent to an interior edge, or
///  - are the target of an incoming boundary edge AND the source of an outgoing boundary edge.
///
/// An intuitive way of looking at this definition is to imagine that the
/// boundary edges form a wall around the subgraph, and the subgraph is given
/// by all nodes and edges that can be reached from within without crossing the
/// wall. The [Direction] of edges (incoming/outgoing) defines which side of
/// the wall is inside, and which is outside.
///
/// If both incoming and outgoing boundary edges are empty, the subgraph is
/// taken to be the entire graph.
///
/// If an invalid subgraph is defined, then behaviour is undefined.
///
/// If any graph method is called with a node or port that is not in the subgraph,
/// the behaviour is unspecified.
#[derive(Debug, Clone, PartialEq)]
pub struct Subgraph<G> {
    /// The base graph.
    graph: G,
    /// All the nodes included in the subgraph.
    nodes: BTreeSet<NodeIndex>,
    /// The ordered list of incoming and outgoing ports in the boundary.
    boundary: Boundary,
}

impl<G: LinkView> Subgraph<G> {
    /// Create a new subgraph view of `graph`.
    ///
    /// ### Arguments
    ///
    /// - `graph`: the graph to take a subgraph from,
    /// - `boundary`: the boundary ports. Incoming ports are incoming boundary edges,
    ///   and outgoing ports are outgoing boundary edges.
    ///
    /// This initialisation is linear in the size of the subgraph.
    pub fn new_subgraph(graph: G, boundary: Boundary) -> Self {
        let nodes = boundary.internal_nodes(&graph).collect();
        Self {
            graph,
            nodes,
            boundary,
        }
    }

    /// Create a new subgraph of `graph` containing only the given nodes.
    ///
    /// The boundary of the subgraph is defined by all ports of the given nodes,
    /// in the order they are given.
    ///
    /// See [`Subgraph::new_subgraph`] for a method that takes an explicit port boundary.
    pub fn with_nodes(graph: G, nodes: impl IntoIterator<Item = NodeIndex>) -> Self {
        let ordered_nodes = nodes.into_iter().collect_vec();
        let nodes = ordered_nodes.iter().copied().collect();
        let boundary = collect_boundary_ports(&graph, ordered_nodes, &nodes);
        Self {
            graph,
            nodes,
            boundary,
        }
    }

    /// Whether the subgraph is convex.
    #[inline]
    pub fn is_convex(&self) -> bool {
        if self.node_count() <= 1 {
            return true;
        }
        let checker = TopoConvexChecker::new(&self.graph);
        self.is_convex_with_checker(&checker)
    }

    /// Whether the subgraph is convex, using a pre-existing checker.
    #[inline]
    pub fn is_convex_with_checker(&self, checker: &impl ConvexChecker) -> bool {
        if self.node_count() <= 1 {
            return true;
        }
        checker.is_convex(
            self.nodes_iter(),
            self.boundary.input_indices().iter().copied(),
            self.boundary.output_indices().iter().copied(),
        )
    }

    /// Utility function to filter out links that are not in the subgraph.
    #[inline(always)]
    fn contains_link(&self, (from, to): (G::LinkEndpoint, G::LinkEndpoint)) -> bool {
        self.contains_endpoint(from) && self.contains_endpoint(to)
    }

    /// Utility function to filter out link endpoints that are not in the subgraph.
    #[inline(always)]
    fn contains_endpoint(&self, e: G::LinkEndpoint) -> bool {
        self.contains_port(e.into())
    }
}

/// Collect all the boundary input and output ports of a set of nodes.
///
/// Ports that connect nodes in the set are not included.
fn collect_boundary_ports<G: LinkView>(
    graph: &G,
    ordered_nodes: impl IntoIterator<Item = NodeIndex>,
    node_set: &BTreeSet<NodeIndex>,
) -> Boundary {
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();

    let has_external_link = |p: &PortIndex| -> bool {
        graph.port_links(*p).any(|(_, lnk)| {
            let neighbour = graph.port_node(lnk).expect("Linked port belongs to a node");
            !node_set.contains(&neighbour)
        })
    };

    for node in ordered_nodes.into_iter() {
        for p in graph.inputs(node).filter(has_external_link) {
            inputs.push(p);
        }
        for p in graph.outputs(node).filter(has_external_link) {
            outputs.push(p);
        }
    }

    Boundary::new(inputs, outputs)
}

impl<G: PortView> PortView for Subgraph<G> {
    #[inline(always)]
    fn contains_node(&'_ self, node: NodeIndex) -> bool {
        self.nodes.contains(&node)
    }

    #[inline(always)]
    fn contains_port(&self, port: PortIndex) -> bool {
        let Some(node) = self.graph.port_node(port) else {
            return false;
        };
        self.contains_node(node)
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    #[inline]
    fn node_count(&self) -> usize {
        self.nodes.len()
    }

    #[inline]
    fn port_count(&self) -> usize {
        self.ports_iter().count()
    }

    #[inline]
    fn nodes_iter(&self) -> impl Iterator<Item = NodeIndex> + Clone {
        self.nodes.iter().copied()
    }

    #[inline]
    fn ports_iter(&self) -> impl Iterator<Item = PortIndex> + Clone {
        self.nodes.iter().flat_map(|&n| self.graph.all_ports(n))
    }

    #[inline]
    fn node_capacity(&self) -> usize {
        self.graph.node_capacity() - self.graph.node_count() + self.node_count()
    }

    #[inline]
    fn port_capacity(&self) -> usize {
        self.graph.port_capacity() - self.graph.port_count() + self.port_count()
    }

    delegate! {
        to self.graph {
            fn port_direction(&self, port: impl Into<PortIndex>) -> Option<Direction>;
            fn port_node(&self, port: impl Into<PortIndex>) -> Option<NodeIndex>;
            fn port_offset(&self, port: impl Into<PortIndex>) -> Option<PortOffset>;
            fn port_index(&self, node: NodeIndex, offset: PortOffset) -> Option<PortIndex>;
            fn ports(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = PortIndex> + Clone;
            fn all_ports(&self, node: NodeIndex) -> impl Iterator<Item = PortIndex> + Clone;
            fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn num_ports(&self, node: NodeIndex, direction: Direction) -> usize;
            fn port_offsets(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = PortOffset> + Clone;
            fn all_port_offsets(&self, node: NodeIndex) -> impl Iterator<Item = PortOffset> + Clone;
            fn node_port_capacity(&self, node: NodeIndex) -> usize;
        }
    }
}

impl<G: LinkView> LinkView for Subgraph<G> {
    type LinkEndpoint = G::LinkEndpoint;

    fn endpoint_port(&self, end: Self::LinkEndpoint) -> PortIndex {
        self.graph.endpoint_port(end)
    }

    fn get_connections(
        &self,
        from: NodeIndex,
        to: NodeIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        if self.nodes.contains(&from) && self.nodes.contains(&to) {
            Either::Left(self.graph.get_connections(from, to))
        } else {
            Either::Right(std::iter::empty())
        }
    }

    fn port_links(
        &self,
        port: PortIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        self.graph
            .port_links(port)
            .filter(|&lnk| self.contains_link(lnk))
    }

    fn links(
        &self,
        node: NodeIndex,
        direction: Direction,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        self.graph
            .links(node, direction)
            .filter(|&lnk| self.contains_link(lnk))
    }

    fn all_links(
        &self,
        node: NodeIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        self.graph
            .all_links(node)
            .filter(|&lnk| self.contains_link(lnk))
    }

    fn neighbours(
        &self,
        node: NodeIndex,
        direction: Direction,
    ) -> impl Iterator<Item = NodeIndex> + Clone {
        self.graph
            .neighbours(node, direction)
            .filter(|&n| self.contains_node(n))
    }

    fn all_neighbours(&self, node: NodeIndex) -> impl Iterator<Item = NodeIndex> + Clone {
        self.graph
            .all_neighbours(node)
            .filter(|&n| self.contains_node(n))
    }

    fn link_count(&self) -> usize {
        self.nodes_iter()
            .flat_map(|node| self.links(node, Direction::Outgoing))
            .count()
    }
}

impl<G: MultiView> MultiView for Subgraph<G>
{
    fn subport_link(&self, subport: Self::LinkEndpoint) -> Option<Self::LinkEndpoint> {
        self.graph
            .subport_link(subport)
            .filter(|&p| self.contains_endpoint(p))
    }

    delegate! {
        to self.graph {
            fn subports(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = Self::LinkEndpoint> + Clone;
            fn all_subports(&self, node: NodeIndex) -> impl Iterator<Item = Self::LinkEndpoint> + Clone;
        }
    }
}

impl<G: LinkMut> Subgraph<G> {
    /// Copies all the nodes and edges in this subgraph into the parent graph.
    /// If there are any boundary edges, these will also be copied but keeping
    /// the same *external* end port (this will fail unless the underlying graph
    /// is a [MultiView]).
    /// Note that Subgraph<Subgraph<MultiPortGraph>>`
    /// thus adds the new nodes to the middle subgraph as well as the outer.
    /// (TODO: test - should happen naturally with right methods, but consider
    /// case where boundary edges of the two subgraphs overlap.)
    ///
    /// Returns a map from node indices within this subgraph, to the indices
    ///    of the newly-created nodes in the parent graph (they are not in this subgraph!);
    /// or a LinkError in which case the underlying graph will not have had any nodes added
    ///    (however subports may have been for a [MultiView]).
    pub fn copy_in_parent(&mut self) -> Result<HashMap<NodeIndex, NodeIndex>, LinkError> {
        self.graph.reserve(self.node_count(), self.port_count());
        let g = &mut self.graph;
        let node_map = self
            .nodes
            .iter()
            .map(|node| (*node, g.add_node(g.num_inputs(*node), g.num_outputs(*node))))
            .collect::<HashMap<_, _>>();
        for (node, new_node) in node_map.iter() {
            for (node_p, other_p) in self.graph.all_links(*node).collect::<Vec<_>>() {
                let new_node_p = self
                    .graph
                    .port_index(*new_node, self.graph.port_offset(node_p).unwrap())
                    .unwrap();
                let new_other_p = match node_map.get(&self.graph.port_node(other_p).unwrap()) {
                    Some(new_other) => {
                        // Internal edge. Add once only, not once per end.
                        if new_other < new_node {
                            continue;
                        }
                        self.graph
                            .port_index(*new_other, self.graph.port_offset(other_p).unwrap())
                            .unwrap()
                    }
                    None => self.graph.endpoint_port(other_p), // Boundary edge. Keep same external endpoint
                };
                if let Err(e) = self.graph.link_ports(new_node_p, new_other_p) {
                    // Must undo insertion
                    for n in node_map.values() {
                        self.graph.remove_node(*n);
                    }
                    return Err(e);
                }
            }
        }
        Ok(node_map)
    }
}

impl<G> HasBoundary for Subgraph<G> {
    fn port_boundary(&self) -> Cow<'_, Boundary> {
        Cow::Borrowed(&self.boundary)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use itertools::Itertools;

    use crate::multiportgraph::SubportIndex;
    use crate::{LinkMut, MultiPortGraph, PortGraph, PortMut, PortView};

    use super::*;

    /// Create the following graph
    ///
    ///  ┌─────┐┌─┐
    ///  │0    ││3│
    ///  └┬───┬┘└┬┘
    ///   │   │  │
    ///  ┌▽─┐┌▽─┐│
    ///  │1 ││2 ││
    ///  └┬┬┘└┬┬┘│
    ///   ││ ┌┘│ │
    ///   │└─│┐│┌┘
    ///   │┌─┘│││
    ///  ┌▽▽┐┌▽▽▽┐
    ///  │5 ││4  │
    ///  └──┘└───┘
    fn graph() -> PortGraph {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 2);
        let n1 = graph.add_node(1, 2);
        let n2 = graph.add_node(1, 2);
        let n3 = graph.add_node(0, 1);
        let n4 = graph.add_node(3, 0);
        let n5 = graph.add_node(2, 0);
        graph.link_nodes(n0, 0, n1, 0).unwrap();
        graph.link_nodes(n0, 1, n2, 0).unwrap();
        graph.link_nodes(n3, 0, n4, 0).unwrap();
        graph.link_nodes(n1, 0, n4, 1).unwrap();
        graph.link_nodes(n2, 1, n4, 2).unwrap();
        graph.link_nodes(n1, 1, n5, 0).unwrap();
        graph.link_nodes(n2, 0, n5, 1).unwrap();
        graph
    }

    #[test]
    fn test_traverse_subgraph_single_node() {
        let graph = graph();
        let (_, n1, _, _, _, _) = (0..6).map(NodeIndex::new).collect_tuple().unwrap();

        // Define the incoming and outgoing boundary edges
        let boundary = Boundary::new(graph.inputs(n1), graph.outputs(n1));

        // Traverse the subgraph
        let nodes: HashSet<_> = boundary.internal_nodes(&graph).collect();

        // Check that the correct nodes and ports were found
        assert_eq!(nodes, [n1].into_iter().collect());
        assert_eq!(boundary.num_ports(), 3);
    }

    #[test]
    fn test_traverse_subgraph_all_but_one_edge() {
        let graph = graph();
        let (_, n1, _, _, n4, _) = (0..6).map(NodeIndex::new).collect_tuple().unwrap();

        // Define both ends of the `1 -> 4` edge as boundary, effectively selecting the whole graph.
        let boundary = Boundary::new(
            [graph.output(n1, 0).unwrap()],
            [graph.input(n4, 1).unwrap()],
        );

        // Traverse the subgraph
        let nodes: HashSet<_> = boundary.internal_nodes(&graph).collect();

        // Check that the correct nodes and ports were found
        assert_eq!(nodes, graph.nodes_iter().collect());
    }

    #[test]
    fn test_traverse_subgraph_basic() {
        let graph = graph();
        let (_, n1, n2, _, _, n5) = (0..6).map(NodeIndex::new).collect_tuple().unwrap();

        // Define the incoming and outgoing boundary edges
        let incoming = [graph.inputs(n1), graph.inputs(n2)].into_iter().flatten();
        let outgoing = [graph.output(n1, 0).unwrap(), graph.output(n2, 1).unwrap()];

        // Traverse the subgraph
        let nodes: HashSet<_> = Boundary::new(incoming, outgoing)
            .internal_nodes(&graph)
            .collect();

        // Check that the correct nodes and ports were found
        assert_eq!(nodes, [n1, n2, n5].into_iter().collect());
    }

    #[test]
    fn test_traverse_subgraph_almost_complete() {
        let graph = graph();
        let (n0, n1, n2, n3, n4, n5) = (0..6).map(NodeIndex::new).collect_tuple().unwrap();

        // Define the incoming and outgoing boundary edges
        let incoming = [
            graph.input(n1, 0).unwrap(),
            graph.input(n4, 2).unwrap(),
            graph.input(n5, 1).unwrap(),
        ];
        let outgoing = [
            graph.output(n0, 0).unwrap(),
            graph.output(n2, 1).unwrap(),
            graph.output(n2, 0).unwrap(),
        ];
        let boundary = Boundary::new(incoming, outgoing);

        // Traverse the subgraph
        let nodes: HashSet<_> = boundary.internal_nodes(&graph).collect();

        // Check that the correct nodes and ports were found
        assert_eq!(nodes, [n0, n1, n2, n3, n4, n5].into_iter().collect());
    }

    #[test]
    fn test_traverse_subgraph_complete() {
        let graph = graph();

        // Traverse the subgraph
        let nodes: HashSet<_> = Boundary::new([], []).internal_nodes(&graph).collect();

        assert_eq!(nodes, graph.nodes_iter().collect());
    }

    #[test]
    fn test_with_nodes() {
        let graph = graph();
        let (_, n1, n2, _, n4, _) = (0..6).map(NodeIndex::new).collect_tuple().unwrap();

        let boundary = Boundary::new(
            [
                graph.input(n1, 0).unwrap(),
                graph.input(n2, 0).unwrap(),
                graph.input(n4, 0).unwrap(),
            ],
            [graph.output(n1, 1).unwrap(), graph.output(n2, 0).unwrap()],
        );
        let from_boundary = Subgraph::new_subgraph(&graph, boundary);

        let from_nodes = Subgraph::with_nodes(&graph, [n1, n2, n4]);

        assert_eq!(from_boundary, from_nodes);
    }

    #[test]
    fn test_properties() {
        let graph = graph();
        let (n0, n1, n2, _n3, n4, _n5) = (0..6).map(NodeIndex::new).collect_tuple().unwrap();
        let subgraph = Subgraph::with_nodes(&graph, [n1, n2, n4]);

        let n1_o0 = subgraph.output(n1, 0).unwrap();
        let n2_o1 = subgraph.output(n2, 1).unwrap();
        let n4_i1 = subgraph.input(n4, 1).unwrap();
        let n4_i2 = subgraph.input(n4, 2).unwrap();

        assert!(!subgraph.is_empty());
        assert_eq!(subgraph.node_count(), 3);
        assert_eq!(subgraph.node_capacity(), graph.node_capacity() - 3);
        assert_eq!(subgraph.port_count(), 9);
        assert_eq!(subgraph.port_capacity(), graph.port_capacity() - 5);
        assert_eq!(
            subgraph.node_port_capacity(n1),
            graph.node_port_capacity(n1)
        );
        assert_eq!(
            subgraph.port_offsets(n1, Direction::Outgoing).collect_vec(),
            graph.port_offsets(n1, Direction::Outgoing).collect_vec()
        );

        assert!(!subgraph.contains_node(n0));
        assert!(subgraph.contains_node(n1));
        assert!(!subgraph.contains_port(graph.output(n0, 0).unwrap()));
        assert!(subgraph.contains_port(n1_o0));

        assert_eq!(subgraph.inputs(n1).count(), 1);
        assert_eq!(subgraph.outputs(n1).count(), 2);
        assert_eq!(subgraph.num_ports(n1, Direction::Incoming), 1);
        assert_eq!(subgraph.num_ports(n1, Direction::Outgoing), 2);
        assert_eq!(subgraph.all_ports(n1).count(), 3);
        assert_eq!(subgraph.all_port_offsets(n1).count(), 3);

        let inputs = subgraph
            .inputs(n1)
            .enumerate()
            .map(|(i, port)| (i, port, Direction::Incoming));
        let outputs = subgraph
            .outputs(n1)
            .enumerate()
            .map(|(i, port)| (i, port, Direction::Outgoing));
        for (i, port, dir) in inputs.chain(outputs) {
            let offset = PortOffset::new(dir, i);
            assert_eq!(subgraph.port_direction(port), Some(dir));
            assert_eq!(subgraph.port_offset(port), Some(offset));
            assert_eq!(subgraph.port_node(port), Some(n1));
            assert_eq!(subgraph.port_index(n1, offset), Some(port));
        }

        // Global iterators
        let nodes = subgraph.nodes_iter().collect_vec();
        assert_eq!(nodes.as_slice(), [n1, n2, n4]);

        let ports = subgraph.ports_iter().collect_vec();
        assert_eq!(ports.len(), subgraph.port_count());

        // Links
        assert!(subgraph.connected(n1, n4));
        assert_eq!(subgraph.link_count(), 2);
        assert_eq!(
            subgraph.output_neighbours(n1).collect_vec().as_slice(),
            [n4]
        );
        assert_eq!(
            subgraph.output_links(n1).collect_vec().as_slice(),
            [(n1_o0, n4_i1)]
        );
        assert_eq!(
            subgraph.port_links(n1_o0).collect_vec().as_slice(),
            [(n1_o0, n4_i1)]
        );
        assert_eq!(
            subgraph.all_links(n4).collect_vec().as_slice(),
            [(n4_i1, n1_o0), (n4_i2, n2_o1),]
        );
        assert_eq!(
            subgraph.get_connections(n1, n4).collect_vec().as_slice(),
            [(n1_o0, n4_i1)]
        );
        assert_eq!(subgraph.get_connections(n0, n1).count(), 0);
        assert_eq!(
            subgraph.all_neighbours(n4).collect_vec().as_slice(),
            [n1, n2]
        );

        // Multiports
        let multigraph = MultiPortGraph::from(graph);
        let subgraph = Subgraph::with_nodes(&multigraph, [n1, n2, n4]);
        let n1_o0 = SubportIndex::new_unique(n1_o0);
        assert_eq!(
            subgraph.all_subports(n1).collect_vec(),
            multigraph.all_subports(n1).collect_vec()
        );
        assert_eq!(
            subgraph.subports(n4, Direction::Incoming).collect_vec(),
            multigraph.subports(n4, Direction::Incoming).collect_vec()
        );
        assert_eq!(subgraph.subport_link(n1_o0), multigraph.subport_link(n1_o0));
    }

    #[test]
    fn test_is_convex() {
        let graph = graph();
        let (n0, n1, n2, _, n4, n5) = (0..6).map(NodeIndex::new).collect_tuple().unwrap();

        let boundary = Boundary::new(graph.inputs(n1), graph.outputs(n1));
        let subg = Subgraph::new_subgraph(&graph, boundary);
        assert!(subg.is_convex());

        let boundary = Boundary::new(
            [graph.input(n4, 1).unwrap()],
            [graph.output(n1, 0).unwrap()],
        );
        let subg = Subgraph::new_subgraph(&graph, boundary);
        assert!(!subg.is_convex());

        // Check the short-circuited case
        let subg = Subgraph::with_nodes(&graph, [n0]);
        assert!(subg.is_convex());
        assert!(subg.is_convex_with_checker(&TopoConvexChecker::new(&graph)));

        // Define the incoming and outgoing boundary edges
        let incoming = [
            graph.input(n1, 0).unwrap(),
            graph.input(n4, 2).unwrap(),
            graph.input(n5, 1).unwrap(),
        ];
        let outgoing = [
            graph.output(n0, 0).unwrap(),
            graph.output(n2, 1).unwrap(),
            graph.output(n2, 0).unwrap(),
        ];
        let boundary = Boundary::new(incoming, outgoing);
        let subg = Subgraph::new_subgraph(&graph, boundary);
        assert!(!subg.is_convex());
    }

    #[test]
    fn test_is_convex_line() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1);
        let n1 = graph.add_node(1, 1);
        let n2 = graph.add_node(1, 0);
        graph.link_nodes(n0, 0, n1, 0).unwrap();
        graph.link_nodes(n1, 0, n2, 0).unwrap();

        let boundary = Boundary::from_ports(
            &graph,
            [graph.output(n0, 0).unwrap(), graph.input(n2, 0).unwrap()],
        );
        let subg = Subgraph::new_subgraph(&graph, boundary);
        assert_eq!(subg.nodes_iter().collect_vec(), [n0, n2]);
        assert!(!subg.is_convex());
    }

    #[test]
    fn test_copy_in_parent() {
        let mut graph = PortGraph::new();
        // First component: n0 -> n1 + cycle
        let n0 = graph.add_node(0, 1);
        let n1 = graph.add_node(2, 1);
        graph.link_nodes(n0, 0, n1, 0).unwrap();
        graph.link_nodes(n1, 0, n1, 1).unwrap();
        // Second component: n2 -> n3
        let n2 = graph.add_node(0, 1);
        let n3 = graph.add_node(1, 0);
        graph.link_nodes(n2, 0, n3, 0).unwrap();
        let backup = graph.clone();

        let mut subg = Subgraph::with_nodes(&mut graph, [n0, n1]);
        let mut node_map = subg.copy_in_parent().unwrap();
        assert_eq!(subg.nodes_iter().collect_vec(), vec![n0, n1]);
        assert_eq!(graph.node_count(), 6);
        let n0_copy = node_map.remove(&n0).unwrap();
        let n1_copy = node_map.remove(&n1).unwrap();
        assert!(node_map.is_empty()); // No other keys
        assert_eq!(
            graph.input_links(n1_copy).collect_vec(),
            vec![
                (
                    graph.input(n1_copy, 0).unwrap(),
                    graph.output(n0_copy, 0).unwrap()
                ),
                (
                    graph.input(n1_copy, 1).unwrap(),
                    graph.output(n1_copy, 0).unwrap()
                )
            ]
        );
        assert_same_for_nodes(&graph, &backup, backup.nodes_iter()); // Rest of graph unchanged
    }

    fn assert_same_for_nodes(
        a: &impl LinkView,
        b: &impl LinkView,
        nodes: impl IntoIterator<Item = NodeIndex>,
    ) {
        for node in nodes {
            assert_eq!(a.num_inputs(node), b.num_inputs(node));
            assert_eq!(a.num_outputs(node), b.num_outputs(node));
            for (a_link, b_link) in a.all_links(node).zip_eq(b.all_links(node)) {
                assert_eq!(a.endpoint_port(a_link.0), b.endpoint_port(b_link.0));
                assert_eq!(a.endpoint_port(a_link.1), b.endpoint_port(b_link.1));
            }
        }
    }

    #[test]
    fn test_copy_in_parent_bad_boundary() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1);
        let n1 = graph.add_node(1, 1);
        let n2 = graph.add_node(1, 0);
        graph.link_nodes(n0, 0, n1, 0).unwrap();
        graph.link_nodes(n1, 0, n2, 0).unwrap();

        let backup = graph.clone();
        let mut subg = Subgraph::with_nodes(&mut graph, [n1, n2]);
        assert!(subg.copy_in_parent().is_err());
        assert_same_for_nodes(&graph, &backup, backup.nodes_iter());
    }

    #[test]
    fn test_copy_in_parent_multi() {
        let mut graph = MultiPortGraph::new();
        let n0 = graph.add_node(0, 1);
        let n1 = graph.add_node(1, 1);
        let n2 = graph.add_node(1, 0);
        graph.link_nodes(n0, 0, n1, 0).unwrap();
        graph.link_nodes(n1, 0, n2, 0).unwrap();
        let backup = graph.clone();

        let mut subg = Subgraph::with_nodes(&mut graph, [n1, n2]);
        let mut node_map = subg.copy_in_parent().unwrap();
        assert_eq!(graph.node_count(), 5);
        let n1_copy = node_map.remove(&n1).unwrap();
        let n2_copy = node_map.remove(&n2).unwrap();
        assert!(node_map.is_empty()); // No other keys
        assert_same_for_nodes(&graph, &backup, [n1, n2]);
        let (sp2, sp1) = graph.all_links(n2_copy).exactly_one().ok().unwrap();
        assert_eq!(sp2.port(), graph.input(n2_copy, 0).unwrap());
        assert_eq!(sp1.port(), graph.output(n1_copy, 0).unwrap());

        let n0_out = graph.output(n0, 0).unwrap();
        assert_eq!(
            graph
                .all_links(n0)
                .map(|(sp1, sp2)| (sp1.port(), sp2.port()))
                .collect_vec(),
            [
                (n0_out, graph.input(n1, 0).unwrap()),
                (n0_out, graph.input(n1_copy, 0).unwrap())
            ]
        );
    }
}
