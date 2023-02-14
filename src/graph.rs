//! Main graph data structure, with components for adjacency, weights, and hierarchical structures.

use thiserror::Error;

use crate::unweighted::{UnweightedGraph};
use crate::weights::Weights;
use crate::{hierarchy::Hierarchy, unweighted};

pub use crate::unweighted::LinkError;
pub use crate::{Direction, NodeIndex, PortIndex, DIRECTIONS};

/// Error returned by [Graph::merge_edges].
#[derive(Debug, Error)]
pub enum MergeEdgesError {
    #[error("unknown edge")]
    UnknownEdge,
    #[error("edge is already connected")]
    AlreadyConnected,
}

#[derive(Debug, Clone, Default)]
pub struct PortGraph<N = (), P = ()> {
    unweighted: UnweightedGraph,
    weights: Weights<N, P>,
    hierarchy: Hierarchy,
}

/// Main weighted portgraph structure.
pub trait Graph<'a, N = (), P = ()>
where
    N: 'a + Clone,
    P: 'a + Clone,
{
    /// Create a new graph with no nodes or edges.
    #[must_use]
    fn new() -> Self;

    /// Create a new graph pre-allocating space for the given number of nodes and edges.
    #[must_use]
    fn with_capacity(nodes: usize, ports: usize) -> Self;

    /// Returns a reference to the underlying unweighted graph.
    #[must_use]
    fn unweighted(&self) -> &UnweightedGraph;

    /// Returns a mutable reference to the underlying unweighted graph.
    #[must_use]
    fn unweighted_mut(&mut self) -> &mut UnweightedGraph;

    /// Returns a reference to the weight component.
    #[must_use]
    fn weights(&self) -> &Weights<N, P>;

    /// Returns a mutable reference to the weight component.
    #[must_use]
    fn weights_mut(&mut self) -> &mut Weights<N, P>;

    /// Returns a reference to the hierarchy component.
    #[must_use]
    fn hierarchy(&self) -> &Hierarchy;

    /// Returns a mutable reference to the hierarchy component.
    #[must_use]
    fn hierarchy_mut(&mut self) -> &mut Hierarchy;

    /// Returns the number of nodes in the graph.
    #[inline(always)]
    #[must_use]
    fn node_count(&self) -> usize {
        self.unweighted().node_count()
    }

    /// Returns the number of ports in the graph.
    #[inline(always)]
    #[must_use]
    fn port_count(&self) -> usize {
        self.unweighted().port_count()
    }

    /// Check whether the graph has a node with a given index.
    #[inline(always)]
    #[must_use]
    fn contains_node(&self, node: NodeIndex) -> bool {
        self.unweighted().contains_node(node)
    }

    /// Check whether the graph has an edge with a given index.
    #[inline(always)]
    #[must_use]
    fn contains_port(&self, port: PortIndex) -> bool {
        self.unweighted().contains_port(port)
    }

    /// Whether the graph has neither nodes nor edges.
    #[inline(always)]
    #[must_use]
    fn is_empty(&self) -> bool {
        self.unweighted().is_empty()
    }

    /// Returns the number of ports for a given node and direction.
    #[inline(always)]
    #[must_use]
    fn node_port_count(&self, _node: NodeIndex, _direction: Direction) -> usize {
        todo!()
    }

    /// Iterate over all nodes in the graph.
    #[inline(always)]
    #[must_use]
    fn nodes_iter(&self) -> unweighted::Nodes {
        self.unweighted().nodes_iter()
    }

    /// Iterate over all nodes in the graph.
    #[inline(always)]
    #[must_use]
    fn ports_iter(&self) -> unweighted::Ports {
        self.unweighted().ports_iter()
    }

    /// Iterate over all the ports of a given node.
    #[inline(always)]
    #[must_use]
    fn ports(&self, node: NodeIndex, direction: Direction) -> unweighted::NodePorts {
        self.unweighted().ports(node, direction)
    }

    /// Iterator over the input ports of a given node.
    #[inline(always)]
    #[must_use]
    fn inputs(&self, node: NodeIndex) -> unweighted::NodePorts {
        self.unweighted().ports(node, Direction::Incoming)
    }

    /// Iterator over the output ports of a given node.
    #[inline(always)]
    #[must_use]
    fn outputs(&self, node: NodeIndex) -> unweighted::NodePorts {
        self.unweighted().ports(node, Direction::Outgoing)
    }

    /// Iterate over all the edges connected to a given node.
    #[inline(always)]
    #[must_use]
    fn neighbours(&self, _node: NodeIndex, _direction: Direction) -> std::iter::Empty<NodeIndex> {
        todo!()
    }

    /// Get the weight of a given node.
    #[inline(always)]
    #[must_use]
    fn node_weight(&'a self, node: NodeIndex) -> &'a N {
        self.weights()
            .try_get_node(node)
            .expect("Node weight was not set")
    }

    /// Get the weight of a given node.
    #[inline(always)]
    #[must_use]
    fn node_weight_mut(&'a mut self, node: NodeIndex) -> &'a mut N {
        self.weights_mut()
            .try_get_node_mut(node)
            .expect("Node weight was not set")
    }

    /// Set the weight of a given node.
    #[inline(always)]
    fn set_node_weight(&mut self, node: NodeIndex, weight: N) {
        self.weights_mut().set_node(node, weight);
    }

    /// Get the weight of a given port.
    #[inline(always)]
    #[must_use]
    fn port_weight(&'a self, port: PortIndex) -> &'a P {
        self.weights()
            .try_get_port(port)
            .expect("Port weight was not set")
    }

    /// Get the weight of a given port.
    #[inline(always)]
    #[must_use]
    fn port_weight_mut(&'a mut self, port: PortIndex) -> &'a mut P {
        self.weights_mut()
            .try_get_port_mut(port)
            .expect("Port weight was not set")
    }

    /// Set the weight of a given port.
    #[inline(always)]
    fn set_port_weight(&mut self, port: PortIndex, weight: P) {
        self.weights_mut().set_port(port, weight);
    }

    /// Adds a node to the portgraph with a given number of input and output ports.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::PortGraph;
    /// let mut g = PortGraph::new();
    /// let node = g.add_node(4, 3);
    /// assert_eq!(g.inputs(node).count(), 4);
    /// assert_eq!(g.outputs(node).count(), 3);
    /// assert!(g.contains_node(node));
    /// ```
    fn add_node(&mut self, weight: N, incoming: usize, outgoing: usize) -> NodeIndex {
        let node = self.unweighted_mut().add_node(incoming, outgoing);
        self.set_node_weight(node, weight);
        node
    }

    /// Adds a node to the portgraph with a given number of input and output ports.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::PortGraph;
    /// let mut g = PortGraph::new();
    /// let node = g.add_node(4, 3);
    /// assert_eq!(g.inputs(node).count(), 4);
    /// assert_eq!(g.outputs(node).count(), 3);
    /// assert!(g.contains_node(node));
    /// ```
    fn add_node_with_ports(
        &mut self,
        weight: N,
        incoming_weights: Vec<P>,
        outgoing_weights: Vec<P>,
    ) -> NodeIndex {
        let node = self.add_node(weight, incoming_weights.len(), outgoing_weights.len());
        for (port, weight) in self.inputs(node).zip(incoming_weights) {
            self.set_port_weight(port, weight);
        }
        for (port, weight) in self.outputs(node).zip(outgoing_weights) {
            self.set_port_weight(port, weight);
        }
        node
    }

    /// Change the number of ports of a given node. If the number of ports is
    /// increased, the port indices of the nodes will be invalidated.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::PortGraph;
    /// let mut g = PortGraph::new();
    /// let node = g.add_node(4, 3);
    /// g.resize_ports(node, 5, 2);
    /// assert_eq!(g.inputs(node).count(), 5);
    /// assert_eq!(g.outputs(node).count(), 2);
    /// ```
    fn resize_ports(&mut self, _node: NodeIndex, _incoming: usize, _outgoing: usize) {
        todo!()
    }

    /// Remove a node from the graph and return its weight.
    fn remove_node(&mut self, node: NodeIndex) -> Option<N> {
        self.unweighted_mut().remove_node(node);
        self.weights_mut().remove_node(node)
    }

    /// Disconnect a port in the graph.
    #[inline(always)]
    fn link_ports(&mut self, from: PortIndex, to: PortIndex) -> Result<(), LinkError> {
        self.unweighted_mut().link_ports(from, to)
    }

    /// Unlinks the `port` and returns the port it was linked to. Returns `None`
    /// when the port was not linked.
    #[inline(always)]
    fn unlink_port(&mut self, port: PortIndex) -> Option<PortIndex> {
        self.unweighted_mut().unlink_port(port)
    }

    // TODO: Missing methods
}

impl<'a, N, P> Graph<'a, N, P> for PortGraph<N, P>
where
    N: 'a + Clone,
    P: 'a + Clone,
{
    fn new() -> Self {
        Self {
            unweighted: UnweightedGraph::new(),
            weights: Weights::new(),
            hierarchy: Hierarchy::new(),
        }
    }

    fn with_capacity(nodes: usize, ports: usize) -> Self {
        Self {
            unweighted: UnweightedGraph::with_capacity(nodes, ports),
            weights: Weights::with_capacity(nodes, ports),
            hierarchy: Hierarchy::new(),
        }
    }

    fn unweighted(&self) -> &UnweightedGraph {
        &self.unweighted
    }

    fn unweighted_mut(&mut self) -> &mut UnweightedGraph {
        &mut self.unweighted
    }

    fn weights(&self) -> &Weights<N, P> {
        &self.weights
    }

    fn weights_mut(&mut self) -> &mut Weights<N, P> {
        &mut self.weights
    }

    fn hierarchy(&self) -> &Hierarchy {
        &self.hierarchy
    }

    fn hierarchy_mut(&mut self) -> &mut Hierarchy {
        &mut self.hierarchy
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        let mut graph: PortGraph<usize, usize, usize> = PortGraph::new();
        assert_eq!(graph.node_count(), 0);
        assert_eq!(graph.edge_count(), 0);
    }
}
