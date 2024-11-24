//! Algorithms for handling port boundaries in a graph.

use std::collections::{HashMap, HashSet};

use super::toposort::toposort;
use crate::{Direction, LinkView, NodeIndex, PortIndex, PortView};

/// A port boundary in a graph.
///
/// Defined
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Boundary {
    /// The ordered list of incoming ports in the boundary.
    inputs: Vec<PortIndex>,
    /// The ordered list of outgoing ports in the boundary.
    outputs: Vec<PortIndex>,
}

/// Boundary port ID.
///
/// See [`Boundary`] for more information.
///
/// The corresponding [`PortIndex`] in the boundary can be retrieved with
/// [`Boundary::port_index`].
#[derive(Debug, Clone, Default, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoundaryPort {
    /// The index of the port in the boundary.
    index: usize,
    /// The direction of the port.
    direction: Direction,
}

/// Trait for graph structures that define a boundary of input and output ports.
pub trait HasBoundary {
    /// Returns the boundary of the node.
    fn port_boundary(&self) -> Boundary;
}

impl Boundary {
    /// Creates a new boundary from the given input and output ports.
    ///
    /// # Panics
    ///
    /// If the direction of the ports does not match the input/output
    /// requirement.
    ///
    /// For an unchecked version, use [`Boundary::new_unchecked`].
    pub fn new(
        graph: &impl PortView,
        inputs: impl IntoIterator<Item = PortIndex>,
        outputs: impl IntoIterator<Item = PortIndex>,
    ) -> Self {
        let inputs = inputs
            .into_iter()
            .inspect(|input| assert_eq!(graph.port_direction(*input), Some(Direction::Incoming)));
        let outputs = outputs
            .into_iter()
            .inspect(|output| assert_eq!(graph.port_direction(*output), Some(Direction::Outgoing)));
        Self::new_unchecked(inputs, outputs)
    }

    /// Creates a new boundary from the given input and output ports.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the ports are correctly specified.
    /// `inputs` must contain only incoming ports, and `outputs` must contain
    /// only outgoing ports.
    ///
    /// For a checked version, use [`Boundary::new`].
    pub fn new_unchecked(
        inputs: impl IntoIterator<Item = PortIndex>,
        outputs: impl IntoIterator<Item = PortIndex>,
    ) -> Self {
        let inputs = inputs.into_iter().collect();
        let outputs = outputs.into_iter().collect();
        Self { inputs, outputs }
    }

    /// Returns the port count in the boundary, both inputs and outputs.
    pub fn num_ports(&self) -> usize {
        self.inputs.len() + self.outputs.len()
    }

    /// Returns the [`BoundaryPort`] corresponding to a port index.
    pub fn port(&self, port: PortIndex, direction: Direction) -> BoundaryPort {
        let ports = match direction {
            Direction::Incoming => &self.inputs,
            Direction::Outgoing => &self.outputs,
        };
        let index = ports
            .iter()
            .position(|&input| input == port)
            .expect("port not found in inputs");
        BoundaryPort { index, direction }
    }

    /// Returns an iterator over the input or output ports in the boundary.
    pub fn ports(&self, dir: Direction) -> impl Iterator<Item = BoundaryPort> {
        let num_ports = match dir {
            Direction::Incoming => self.inputs.len(),
            Direction::Outgoing => self.outputs.len(),
        };
        (0..num_ports).map(move |index| BoundaryPort {
            index,
            direction: dir,
        })
    }

    /// Returns an iterator over the input ports in the boundary.
    #[inline]
    pub fn inputs(&self) -> impl Iterator<Item = BoundaryPort> {
        self.ports(Direction::Incoming)
    }

    /// Returns an iterator over the output ports in the boundary.
    #[inline]
    pub fn outputs(&self) -> impl Iterator<Item = BoundaryPort> {
        self.ports(Direction::Outgoing)
    }

    /// Returns the [`PortIndex`] corresponding to a [`BoundaryPort`] in this boundary.
    pub fn port_index(&self, port: &BoundaryPort) -> PortIndex {
        match port.direction {
            Direction::Incoming => self.inputs[port.index],
            Direction::Outgoing => self.outputs[port.index],
        }
    }

    /// Returns `true` if the other boundary contains the same amount of input
    /// and output ports as this boundary.
    ///
    /// When two boundaries are compatible, [`BoundaryPort`]s that are valid in
    /// one boundary are also valid in the other boundary.
    pub fn is_compatible(&self, other: &Boundary) -> bool {
        self.inputs.len() == other.inputs.len() && self.outputs.len() == other.outputs.len()
    }

    /// Computes a partial order between the ports of a boundary.
    ///
    /// Returns a map indicating for each input port in the boundary, the set of
    /// output ports that can be reached from it in the graph.
    ///
    /// The `graph` parameter must be a valid graph for this boundary. When
    /// multiple nodes not reachable from the boundary are present, consider
    /// using a [`crate::view::Subgraph`] to restrict the traversal.
    ///
    /// # Complexity
    ///
    /// The complexity of this operation is `O(e log(n) + k*n)`, where `e` is
    /// the number of links in the `graph`, is the number of nodes, and `k` is
    /// the number of ports in the boundary.
    pub fn port_ordering(&self, graph: &impl LinkView) -> PortOrdering {
        // Maps between the input/output ports in the boundary and the nodes they belong to.
        let mut input_nodes: HashMap<NodeIndex, Vec<PortIndex>> = HashMap::new();
        let mut output_nodes: HashMap<NodeIndex, Vec<PortIndex>> = HashMap::new();
        for &port in self.inputs.iter() {
            let node = graph.port_node(port).unwrap();
            input_nodes.entry(node).or_default().push(port);
        }
        for &port in self.outputs.iter() {
            let node = graph.port_node(port).unwrap();
            output_nodes.entry(node).or_default().push(port);
        }

        let mut ordering = PortOrdering::new(self.inputs.len(), self.outputs.len());

        // Toposort the subgraph, and collect the reaching input ports for each node.
        // We keep track of how many output neighbors remain to be visited, so we can
        // trim the `reaching` set when we reach the last one.

        // We have to start the toposort from the input nodes that do not have predecessors.
        let source_nodes = input_nodes
            .keys()
            .copied()
            .filter(|&node| graph.input_neighbours(node).count() == 0);

        let mut reaching: HashMap<NodeIndex, (usize, HashSet<PortIndex>)> =
            HashMap::with_capacity(self.num_ports());
        for node in toposort::<_, HashSet<PortIndex>>(graph, source_nodes, Direction::Outgoing) {
            // Collect the reaching ports, plus any ports in the node itself.
            let mut reaching_ports: HashSet<PortIndex> = input_nodes
                .get(&node)
                .into_iter()
                .flatten()
                .copied()
                .collect();

            // Add the reaching ports from the input neighbours.
            for input_neigh in graph.input_neighbours(node) {
                let (output_neighs, input_reaching) = reaching
                    .get_mut(&input_neigh)
                    .expect("Incoming neighbour not visited");
                reaching_ports.extend(input_reaching.iter().copied());
                *output_neighs -= 1;
                // Not reeded anymore, remove from the map.
                if *output_neighs == 0 {
                    reaching.remove(&input_neigh);
                }
            }

            // If there are output boundary ports in the node, add the order relations.
            for &out_port in output_nodes.get(&node).into_iter().flatten() {
                for &in_port in &reaching_ports {
                    ordering.add_order(
                        self.port(in_port, Direction::Incoming),
                        self.port(out_port, Direction::Outgoing),
                    );
                }
            }

            let output_neighs = graph.output_neighbours(node).count();
            reaching.insert(node, (output_neighs, reaching_ports));
        }

        ordering
    }

    /// Given another compatible boundary (see [`Boundary::is_compatible`]),
    /// returns `true` if this boundary is stronger than the other boundary.
    ///
    /// A boundary `B` is stronger than another boundary `C` if for every pair
    /// of input/output ports `(i, o)` where `o` is reachable from `i` in `C`,
    /// `o` is also reachable from `i` in `B`.
    ///
    /// See [`PortOrdering::is_stronger_than`] for more information.
    pub fn is_stronger_than(
        &self,
        other: &Boundary,
        self_graph: &impl LinkView,
        other_graph: &impl LinkView,
    ) -> bool {
        let self_ordering = self.port_ordering(self_graph);
        let other_ordering = other.port_ordering(other_graph);
        self_ordering.is_stronger_than(&other_ordering)
    }
}

/// A relation between input ports and output ports in a boundary that contains
/// a pair of ports `(i, o)` when `o` is reachable from `i` in the graph.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PortOrdering {
    /// For each input port, the set of output ports that can be reached from it.
    reachable: Vec<HashSet<BoundaryPort>>,
    /// For each output port, the set of input ports from which it can be reached.
    reaching: Vec<HashSet<BoundaryPort>>,
}

impl PortOrdering {
    /// Map a [`BoundaryPort`] to its index in the `reachable` and `reaching`
    /// vectors.
    fn index(&self, port: BoundaryPort) -> usize {
        port.index
    }

    /// Returns the set of ports that can be reached from the given port.
    pub fn reachable_ports(&self, port: BoundaryPort) -> &HashSet<BoundaryPort> {
        debug_assert_eq!(port.direction, Direction::Incoming);
        &self.reachable[self.index(port)]
    }

    /// Returns the set of ports from which the given port can be reached.
    pub fn reaching_ports(&self, port: BoundaryPort) -> &HashSet<BoundaryPort> {
        debug_assert_eq!(port.direction, Direction::Outgoing);
        &self.reaching[self.index(port)]
    }

    /// Returns `true` if this relation is stronger than the other relation.
    ///
    /// A relation `P` is stronger than another `Q` if for every pair `(i, o)` in `Q`,
    /// `P` also contains the pair.
    pub fn is_stronger_than(&self, other: &Self) -> bool {
        if self.reachable.len() != other.reachable.len()
            || self.reaching.len() != other.reaching.len()
        {
            panic!("Incompatible port orderings");
        }

        for (self_reachable, other_reachable) in self.reachable.iter().zip(other.reachable.iter()) {
            if other_reachable
                .iter()
                .any(|port| !self_reachable.contains(port))
            {
                return false;
            }
        }

        true
    }

    /// Returns the list of port pairs in `other` that are not present in `self`.
    ///
    /// This list is empty if and only if `self` is stronger than `other`.
    /// See [`PortOrdering::is_stronger_than`] for more information.
    pub fn missing_pairs<'a>(
        &'a self,
        other: &'a Self,
    ) -> impl Iterator<Item = (BoundaryPort, BoundaryPort)> + 'a {
        if self.reachable.len() != other.reachable.len()
            || self.reaching.len() != other.reaching.len()
        {
            panic!("Incompatible port orderings");
        }

        self.reachable
            .iter()
            .zip(other.reachable.iter())
            .enumerate()
            .flat_map(|(i, (self_reachable, other_reachable))| {
                let input = BoundaryPort {
                    index: i,
                    direction: Direction::Incoming,
                };
                other_reachable
                    .iter()
                    .filter(|port| !self_reachable.contains(port))
                    .map(move |port| (input, *port))
            })
    }

    /// Returns a new empty ordering.
    pub(self) fn new(num_inputs: usize, num_outputs: usize) -> Self {
        Self {
            reachable: vec![HashSet::new(); num_inputs],
            reaching: vec![HashSet::new(); num_outputs],
        }
    }

    /// Add a link to the ordering.
    pub(self) fn add_order(&mut self, from: BoundaryPort, to: BoundaryPort) {
        debug_assert_eq!(from.direction, Direction::Incoming);
        debug_assert_eq!(to.direction, Direction::Outgoing);

        let from_index = self.index(from);
        let to_index = self.index(to);
        self.reachable[from_index].insert(to);
        self.reaching[to_index].insert(from);
    }
}

#[cfg(test)]
mod test {
    use crate::view::Subgraph;
    use crate::{LinkMut, MultiPortGraph, PortMut};

    use super::*;
    use itertools::Itertools;
    use rstest::{fixture, rstest};

    /// A complete bipartite graph with `N` input nodes and `M` output nodes.
    ///
    /// Each input node is connected to all output nodes.
    ///
    /// Returns the graph and the input and output nodes arrays.
    #[fixture]
    fn graph_kn<const N: usize, const M: usize>() -> (MultiPortGraph, [NodeIndex; N], [NodeIndex; M])
    {
        let mut graph = MultiPortGraph::new();
        let inputs: [NodeIndex; N] = (0..N)
            .map(|_| graph.add_node(1, M))
            .collect_vec()
            .try_into()
            .unwrap();
        let outputs: [NodeIndex; M] = (0..M)
            .map(|_| graph.add_node(N, 1))
            .collect_vec()
            .try_into()
            .unwrap();

        for (i, &input) in inputs.iter().enumerate() {
            for (j, &output) in outputs.iter().enumerate() {
                graph.link_nodes(input, j, output, i).unwrap();
            }
        }

        (graph, inputs, outputs)
    }

    /// Test DAG
    ///
    /// ```text
    /// 0 -> 1 -> 2 -> 3
    ///      | \  |
    ///      v  \ v
    /// 4 -> 5 -> 6 -> 7
    /// ```
    #[fixture]
    fn graph() -> MultiPortGraph {
        let mut graph = MultiPortGraph::new();
        let nodes: Vec<NodeIndex> = (0..8).map(|_| graph.add_node(4, 4)).collect();
        // Horizontal links between from port 0 to port 0
        graph.link_nodes(nodes[0], 0, nodes[1], 0).unwrap();
        graph.link_nodes(nodes[1], 0, nodes[2], 0).unwrap();
        graph.link_nodes(nodes[2], 0, nodes[3], 0).unwrap();
        graph.link_nodes(nodes[4], 0, nodes[5], 0).unwrap();
        graph.link_nodes(nodes[5], 0, nodes[6], 0).unwrap();
        graph.link_nodes(nodes[6], 0, nodes[7], 0).unwrap();
        // Other ports
        graph.link_nodes(nodes[1], 1, nodes[5], 1).unwrap();
        graph.link_nodes(nodes[2], 1, nodes[6], 0).unwrap();
        graph.link_nodes(nodes[1], 2, nodes[6], 2).unwrap();

        graph
    }

    #[rstest]
    fn test_boundary_new(graph: MultiPortGraph) {
        let nodes = graph.nodes_iter().collect_vec();

        // Create a boundary containing the {1,2,5,6} subgraph.
        let boundary = Boundary::new(
            &graph,
            [
                graph.input(nodes[1], 0).unwrap(),
                graph.input(nodes[5], 0).unwrap(),
            ],
            [
                graph.output(nodes[2], 0).unwrap(),
                graph.output(nodes[6], 0).unwrap(),
            ],
        );
        let subgraph = Subgraph::with_nodes(&graph, [nodes[1], nodes[2], nodes[5], nodes[6]]);
        assert_eq!(boundary, subgraph.port_boundary());
        assert_eq!(boundary.num_ports(), 4);
        assert_eq!(
            boundary.port(graph.input(nodes[5], 0).unwrap(), Direction::Incoming),
            BoundaryPort {
                index: 1,
                direction: Direction::Incoming
            }
        );
        assert_eq!(boundary.ports(Direction::Incoming).count(), 2);
    }

    #[rstest]
    fn test_port_ordering(graph: MultiPortGraph) {
        let nodes = graph.nodes_iter().collect_vec();
        let subgraph = Subgraph::with_nodes(&graph, [nodes[1], nodes[2], nodes[5], nodes[6]]);
        let boundary = subgraph.port_boundary();

        let (in_0, in_1) = boundary.inputs().collect_tuple().unwrap();
        let (out_0, out_1) = boundary.outputs().collect_tuple().unwrap();

        let ordering = boundary.port_ordering(&subgraph);
        assert_eq!(
            ordering
                .reachable_ports(in_0)
                .iter()
                .copied()
                .sorted()
                .collect_vec()
                .as_slice(),
            [out_0, out_1]
        );
        assert_eq!(
            ordering
                .reachable_ports(in_1)
                .iter()
                .copied()
                .collect_vec()
                .as_slice(),
            [out_1]
        );
        assert_eq!(
            ordering
                .reaching_ports(out_0)
                .iter()
                .copied()
                .collect_vec()
                .as_slice(),
            [in_0]
        );
        assert_eq!(
            ordering
                .reaching_ports(out_1)
                .iter()
                .copied()
                .sorted()
                .collect_vec()
                .as_slice(),
            [in_0, in_1]
        );
    }

    #[rstest]
    fn test_order_comparison(graph: MultiPortGraph) {
        let nodes = graph.nodes_iter().collect_vec();
        let subgraph = Subgraph::with_nodes(&graph, [nodes[1], nodes[2], nodes[5], nodes[6]]);
        let boundary = subgraph.port_boundary();

        let (graph_22, ins_22, outs_22) = graph_kn::<2, 2>();
        let boundary_22 = Boundary::new(
            &graph_22,
            [
                graph_22.input(ins_22[0], 0).unwrap(),
                graph_22.input(ins_22[1], 0).unwrap(),
            ],
            [
                graph_22.output(outs_22[0], 0).unwrap(),
                graph_22.output(outs_22[1], 0).unwrap(),
            ],
        );

        assert!(boundary.is_compatible(&boundary_22));
        assert!(boundary_22.is_compatible(&boundary));

        let ordering = boundary.port_ordering(&subgraph);
        let ordering_22 = boundary_22.port_ordering(&graph_22);

        assert!(!ordering.is_stronger_than(&ordering_22));
        assert!(ordering_22.is_stronger_than(&ordering));
        assert!(!boundary.is_stronger_than(&boundary_22, &subgraph, &graph_22));
        assert!(boundary_22.is_stronger_than(&boundary, &graph_22, &subgraph));
    }
}
