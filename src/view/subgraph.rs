//! Views into non-hierarchical parts of `PortView`s.

use std::collections::BTreeSet;

use crate::{algorithms::ConvexChecker, Direction, LinkView, NodeIndex, PortIndex, PortView};

use super::filter::FilteredGraph;

type NodeCallback = fn(NodeIndex, &SubgraphContext) -> bool;
type PortCallback = fn(PortIndex, &SubgraphContext) -> bool;

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
/// wall. The directedness of edges (incoming/outgoing) defines which side of
/// the wall is inside, and which is outside.
///
/// If both incoming and outgoing boundary edges are empty, the subgraph is
/// taken to be the entire graph.
///
/// If an invalid subgraph is defined, then behaviour is undefined.
///
/// At initialisation, this performs a one-off expensive computation (linear in
/// the size of the subgraph) to determine the nodes that are in the subgraph.
pub type Subgraph<'g, G> = FilteredGraph<'g, G, NodeCallback, PortCallback, SubgraphContext>;

/// Internal context used in the [`Subgraph`] adaptor.
#[derive(Debug, Clone)]
pub struct SubgraphContext {
    nodes: BTreeSet<NodeIndex>,
    ports: BTreeSet<PortIndex>,
    inputs: Vec<PortIndex>,
    outputs: Vec<PortIndex>,
}

impl<'a, G: LinkView> Subgraph<'a, G> {
    /// Create a new subgraph view of `graph`.
    ///
    /// ### Arguments
    ///
    /// - `graph`: the graph to take a subgraph from,
    /// - `boundary`: the boundary ports. Incoming ports are incoming boundary edges,
    /// and outgoing ports are outgoing boundary edges.
    ///
    /// This initialisation is linear in the size of the subgraph.
    pub fn new_subgraph(graph: &'a G, boundary: impl IntoIterator<Item = PortIndex>) -> Self {
        let mut inputs = Vec::new();
        let mut outputs = Vec::new();

        let boundary = boundary.into_iter().map(|p| {
            match graph.port_direction(p).unwrap() {
                Direction::Incoming => inputs.push(p),
                Direction::Outgoing => outputs.push(p),
            };
            p
        });

        let (nodes, ports) = traverse_subgraph(graph, boundary);
        let context = SubgraphContext {
            nodes: nodes.into_iter().collect(),
            ports: ports.into_iter().collect(),
            inputs,
            outputs,
        };
        Self::new(
            graph,
            |n, ctx| ctx.nodes.contains(&n),
            |p, ctx| ctx.ports.contains(&p),
            context,
        )
    }

    /// Whether the subgraph is convex.
    pub fn is_convex(&self) -> bool {
        let mut checker = ConvexChecker::new(self.graph());
        self.is_convex_with_checker(&mut checker)
    }

    /// Whether the subgraph is convex, using a pre-existing checker.
    pub fn is_convex_with_checker(&self, checker: &mut ConvexChecker<&G>) -> bool {
        checker.is_convex(
            self.nodes_iter(),
            self.context().inputs.iter().copied(),
            self.context().outputs.iter().copied(),
        )
    }
}

/// Traverse the subgraph defined by the boundary edges.
///
/// Start just inside the boundaries and follow each edge that is not itself
/// a boundary.
fn traverse_subgraph<G: LinkView>(
    graph: &G,
    boundary: impl IntoIterator<Item = PortIndex>,
) -> (BTreeSet<NodeIndex>, BTreeSet<PortIndex>) {
    // Nodes within subgraph
    let mut nodes = BTreeSet::new();
    // Ports within subgraph
    let mut ports = BTreeSet::new();
    // For every visited edge, we mark both ports as visited
    let mut visited = BTreeSet::new();

    // The set of nodes to traverse
    let mut nodes_to_process: BTreeSet<_> = boundary
        .into_iter()
        .map(|p| {
            let this_node = graph.port_node(p).unwrap();
            if let Some(other_port) = graph.port_link(p) {
                visited.insert(other_port.into());
            }
            visited.insert(p);
            this_node
        })
        .collect();

    if nodes_to_process.is_empty() {
        // Edge case: no boundary edges, so the subgraph is the entire graph
        nodes_to_process = graph.nodes_iter().collect();
    }

    while let Some(node) = nodes_to_process.pop_first() {
        nodes.insert(node);
        // Traverse every unvisited edge in `node`
        for p in graph.all_ports(node) {
            if visited.insert(p) {
                // Visit it
                ports.insert(p);
                if let Some(other_port) = graph.port_link(p) {
                    visited.insert(other_port.into());
                    ports.insert(other_port.into());
                    // Possibly a new node!
                    let other_node = graph.port_node(other_port).unwrap();
                    nodes_to_process.insert(other_node);
                }
            }
        }
    }

    (nodes, ports)
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use crate::{LinkMut, PortGraph, PortMut, PortView};

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
        let boundary = graph.all_ports(n1);

        // Traverse the subgraph
        let (nodes, ports) = traverse_subgraph(&graph, boundary);

        // Check that the correct nodes and ports were found
        assert_eq!(nodes, [n1].into_iter().collect());
        assert!(ports.is_empty());
    }

    #[test]
    fn test_traverse_subgraph_all_but_one_edge() {
        let graph = graph();
        let (_, n1, _, _, n4, _) = (0..6).map(NodeIndex::new).collect_tuple().unwrap();

        // Define the incoming and outgoing boundary edges
        let boundary = [graph.output(n1, 0).unwrap(), graph.input(n4, 1).unwrap()];

        // Traverse the subgraph
        let (nodes, ports) = traverse_subgraph(&graph, boundary);

        // Check that the correct nodes and ports were found
        assert_eq!(nodes, graph.nodes_iter().collect());
        assert_eq!(ports.len(), graph.port_count() - 2);
    }

    #[test]
    fn test_traverse_subgraph_basic() {
        let graph = graph();
        let (_, n1, n2, _, _, n5) = (0..6).map(NodeIndex::new).collect_tuple().unwrap();

        // Define the incoming and outgoing boundary edges
        let incoming = [graph.inputs(n1), graph.inputs(n2)].into_iter().flatten();
        let outgoing = [graph.output(n1, 0).unwrap(), graph.output(n2, 1).unwrap()];

        // Traverse the subgraph
        let (nodes, ports) = traverse_subgraph(&graph, incoming.chain(outgoing));

        // Check that the correct nodes and ports were found
        assert_eq!(nodes, [n1, n2, n5].into_iter().collect());
        assert_eq!(ports.len(), 4)
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
        let boundary = incoming.into_iter().chain(outgoing);

        // Traverse the subgraph
        let (nodes, ports) = traverse_subgraph(&graph, boundary);

        // Check that the correct nodes and ports were found
        assert_eq!(nodes, [n0, n1, n2, n3, n4, n5].into_iter().collect());
        assert_eq!(
            ports,
            [
                vec![graph.output(n0, 1).unwrap()],
                graph.outputs(n1).collect(),
                graph.inputs(n2).collect(),
                graph.all_ports(n3).collect(),
                vec![graph.input(n4, 0).unwrap(), graph.input(n4, 1).unwrap()],
                vec![graph.input(n5, 0).unwrap()],
            ]
            .into_iter()
            .flatten()
            .collect()
        );
    }

    #[test]
    fn test_traverse_subgraph_complete() {
        let graph = graph();

        // Traverse the subgraph
        let (nodes, ports) = traverse_subgraph(&graph, []);

        assert_eq!(nodes, graph.nodes_iter().collect());
        assert_eq!(ports, graph.ports_iter().collect());
    }

    #[test]
    fn test_is_convex() {
        let graph = graph();
        let (n0, n1, n2, _, n4, n5) = (0..6).map(NodeIndex::new).collect_tuple().unwrap();

        let boundary = graph.all_ports(n1);
        let subg = Subgraph::new_subgraph(&graph, boundary);
        assert!(subg.is_convex());

        let boundary = [graph.output(n1, 0).unwrap(), graph.input(n4, 1).unwrap()];
        let subg = Subgraph::new_subgraph(&graph, boundary);
        assert!(!subg.is_convex());

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
        let boundary = incoming.into_iter().chain(outgoing);
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

        let boundary = [graph.output(n0, 0).unwrap(), graph.input(n2, 0).unwrap()];
        let subg = Subgraph::new_subgraph(&graph, boundary);
        assert_eq!(subg.nodes_iter().collect_vec(), [n0, n2]);
        assert!(!subg.is_convex());
    }
}
