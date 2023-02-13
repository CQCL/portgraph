//! Main graph data structure, with components for adjacency, weights, and hierarchical structures.

use thiserror::Error;

use crate::unweighted::UnweightedGraph;
use crate::weights::Weights;
use crate::{hierarchy::Hierarchy, unweighted};

pub use crate::{Direction, EdgeIndex, NodeIndex, PortIndex, DIRECTIONS};

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
pub trait Graph<N = (), P = ()>
where
    N: Default,
    P: Default,
{
    /// Create a new graph with no nodes or edges.
    fn new() -> Self;

    /// Create a new graph pre-allocating space for the given number of nodes and edges.
    fn with_capacity(nodes: usize, ports: usize) -> Self;

    /// Returns a reference to the underlying unweighted graph.
    fn unweighted(&self) -> &UnweightedGraph;

    /// Returns a mutable reference to the underlying unweighted graph.
    fn unweighted_mut(&mut self) -> &mut UnweightedGraph;

    /// Returns a reference to the weight component.
    fn weights(&self) -> &Weights<N, P>;

    /// Returns a mutable reference to the weight component.
    fn weights_mut(&mut self) -> &mut Weights<N, P>;

    /// Returns a reference to the hierarchy component.
    fn hierarchy(&self) -> &Hierarchy;

    /// Returns a mutable reference to the hierarchy component.
    fn hierarchy_mut(&mut self) -> &mut Hierarchy;

    /// Returns the number of nodes in the graph.
    #[inline(always)]
    fn node_count(&self) -> usize {
        self.unweighted().node_count()
    }

    /// Returns the number of ports in the graph.
    #[inline(always)]
    fn port_count(&self) -> usize {
        self.unweighted().port_count()
    }

    /// Check whether the graph has a node with a given index.
    #[inline(always)]
    fn has_node(&self, _node: NodeIndex) -> bool {
        todo!()
    }

    /// Check whether the graph has an edge with a given index.
    #[inline(always)]
    fn has_port(&self, _port: PortIndex) -> bool {
        todo!()
    }

    /// Whether the graph has neither nodes nor edges.
    #[inline(always)]
    fn is_empty(&self) -> bool {
        self.unweighted().is_empty()
    }

    /// Returns the number of ports for a given node and direction.
    #[inline(always)]
    fn node_port_count(&self, _node: NodeIndex, _direction: Direction) -> usize {
        todo!()
    }

    /// Iterate over all nodes in the graph.
    #[inline(always)]
    fn nodes_iter(&self) -> unweighted::Nodes {
        self.unweighted().nodes_iter()
    }

    /// Iterate over all nodes in the graph.
    #[inline(always)]
    fn ports_iter(&self) -> unweighted::Ports {
        self.unweighted().ports_iter()
    }

    /// Iterate over all the ports of a given node.
    #[inline(always)]
    fn ports(&self, node: NodeIndex, direction: Direction) -> unweighted::NodePorts {
        self.unweighted().ports(node, direction)
    }

    /// Iterate over all the edges connected to a given node.
    #[inline(always)]
    fn edges(&self, _node: NodeIndex, _direction: Direction) -> std::iter::Empty<EdgeIndex> {
        todo!()
    }

    /// Remove a node from the graph and return its weight.
    fn remove_node(&mut self, node: NodeIndex) -> Option<N> {
        self.unweighted_mut()
            .remove_node(node);
        self.weights_mut().try_get_node_mut(node).map(|w| std::mem::replace(w, N::default()))
    }

    /// Disconnect a port in the graph.
    #[inline(always)]
    fn disconnect_port(&mut self, _port: PortIndex) {
        todo!()
    }

    // TODO: Missing methods
}

impl<N, P> Graph<N, P> for PortGraph<N, P>
where
    N: Default,
    P: Default,
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
