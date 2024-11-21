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
        let inputs = inputs.into_iter().map(|input| {
            assert_eq!(graph.port_direction(input), Some(Direction::Incoming));
            input
        });
        let outputs = outputs.into_iter().map(|output| {
            assert_eq!(graph.port_direction(output), Some(Direction::Outgoing));
            output
        });
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
    /// using a [`Subgraph`] to restrict the traversal.
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
        let mut reaching: HashMap<NodeIndex, (usize, HashSet<PortIndex>)> =
            HashMap::with_capacity(self.num_ports());
        for node in toposort::<_, HashSet<PortIndex>>(
            graph,
            input_nodes.keys().copied(),
            Direction::Outgoing,
        ) {
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
                *output_neighs = *output_neighs - 1;
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
            .map(|(i, (self_reachable, other_reachable))| {
                let input = BoundaryPort {
                    index: i,
                    direction: Direction::Incoming,
                };
                other_reachable
                    .iter()
                    .filter(|port| !self_reachable.contains(port))
                    .map(move |port| (input, *port))
            })
            .flatten()
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
