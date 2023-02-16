//! Main graph data structure, with components for adjacency, weights, and hierarchical structures.

use std::iter;

use thiserror::Error;

use crate::hierarchy;
use crate::weights::Weights;
use crate::{hierarchy::Hierarchy, unweighted};

pub use crate::unweighted::{LinkError, UnweightedGraph};
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

/// Main weighted graph interface, non-mutable operations.
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

    /// Returns a reference to the weight component.
    #[must_use]
    fn weights(&self) -> &Weights<N, P>;

    /// Returns a reference to the hierarchy component.
    #[must_use]
    fn hierarchy(&self) -> &Hierarchy;

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

    /// Returns the number of edges in the graph, corresponding to the number of
    /// links between ports.
    #[inline(always)]
    #[must_use]
    fn edge_count(&self) -> usize {
        todo!()
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

    /// Get the port index of a given node, direction, and offset.
    #[inline(always)]
    #[must_use]
    fn port_index(
        &self,
        node: NodeIndex,
        offset: usize,
        direction: Direction,
    ) -> Option<PortIndex> {
        self.ports(node, direction).nth(offset)
    }

    /// Get the port offset in the corresponding node.
    #[inline(always)]
    #[must_use]
    fn port_offset(&self, port: PortIndex) -> Option<usize> {
        self.unweighted().port_index(port)
    }

    /// Get the input port index of a given node and offset.
    #[inline(always)]
    #[must_use]
    fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.port_index(node, offset, Direction::Incoming)
    }

    /// Get the output port index of a given node and offset.
    #[inline(always)]
    #[must_use]
    fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.port_index(node, offset, Direction::Outgoing)
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

    /// Slice of all the links of the `node` in the given `direction`. When the
    /// corresponding node port is linked to another one, the Option contains
    /// the index of the other port.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::{PortGraph, GraphMut, Graph, Direction};
    /// let mut graph = PortGraph::<(),()>::new();
    ///
    /// let node_a = graph.add_node((), 0, 2);
    /// let node_b = graph.add_node((), 1, 0);
    ///
    /// let port_a = graph.output(node_a, 0).unwrap();
    /// let port_b = graph.input(node_b, 0).unwrap();
    ///
    /// graph.link_ports(port_a, port_b).unwrap();
    ///
    /// assert_eq!(graph.links(node_a, Direction::Outgoing), &[Some(port_b), None]);
    /// assert_eq!(graph.links(node_b, Direction::Incoming), &[Some(port_a)]);
    /// ```
    #[inline]
    fn links(&self, node: NodeIndex, direction: Direction) -> &[Option<PortIndex>] {
        self.unweighted().links(node, direction)
    }

    /// Slice of all the input links of the `node`. Shorthand for [`Graph::links`].
    #[inline]
    fn input_links(&self, node: NodeIndex) -> &[Option<PortIndex>] {
        self.unweighted().input_links(node)
    }

    /// Slice of all the output links of the `node`. Shorthand for [`Graph::links`].
    #[inline]
    fn output_links(&self, node: NodeIndex) -> &[Option<PortIndex>] {
        self.unweighted().output_links(node)
    }

    /// Iterate over all the edges connected to a given node.
    #[inline(always)]
    fn neighbours(&self, _node: NodeIndex, _direction: Direction) -> std::iter::Empty<NodeIndex> {
        todo!()
    }

    /// Check whether two nodes are connected. Return the port indices of the first edge found.
    #[must_use]
    fn connected(&self, from: NodeIndex, to: NodeIndex) -> Option<(PortIndex, PortIndex)> {
        self.outputs(from)
            .filter_map(|from_port| {
                self.port_link(from_port)
                    .filter(|to_port| self.port_node(*to_port) == Some(to))
                    .map(|to_port| (from_port, to_port))
            })
            .next()
    }

    /// Get the node of a given port.
    #[inline(always)]
    #[must_use]
    fn port_node(&self, port: PortIndex) -> Option<NodeIndex> {
        self.unweighted().port_node(port)
    }

    /// Get the weight of a given node.
    #[inline(always)]
    #[must_use]
    fn node_weight(&'a self, node: NodeIndex) -> Option<&'a N> {
        self.weights().try_get_node(node)
    }

    /// Iterate over the node weights of a graph.
    fn node_weights(&'a self) -> iter::Empty<(NodeIndex, &'a N)> {
        todo!()
    }

    /// Get the weight of a given port.
    #[inline(always)]
    #[must_use]
    fn port_weight(&'a self, port: PortIndex) -> Option<&'a P> {
        self.weights().try_get_port(port)
    }

    /// Iterate over the port weights of a graph.
    fn port_weights(&'a self) -> iter::Empty<(PortIndex, &'a N)> {
        todo!()
    }

    /// Get the port linked to the given port. Returns `None` if the port is not linked.
    #[inline(always)]
    #[must_use]
    fn port_link(&self, port: PortIndex) -> Option<PortIndex> {
        self.unweighted().port_link(port)
    }

    /// Whether the port is linked to the another port.
    #[inline(always)]
    #[must_use]
    fn is_linked(&self, port: PortIndex) -> bool {
        self.port_link(port).is_some()
    }

    /// Returns the number of children of a node in the hierarchy.
    #[inline(always)]
    #[must_use]
    fn node_child_count(&self, node: NodeIndex) -> usize {
        self.hierarchy().child_count(node)
    }

    /// Get the parent of a node in the hierarchy.
    #[inline(always)]
    #[must_use]
    fn node_parent(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.hierarchy().parent(node)
    }

    /// Get the first child of a node in the hierarchy.
    #[inline(always)]
    #[must_use]
    fn node_first_child(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.hierarchy().first(node)
    }

    /// Get the last child of a node in the hierarchy.
    #[inline(always)]
    #[must_use]
    fn node_last_child(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.hierarchy().last(node)
    }

    /// Iterate over the children of a node in the hierarchy.
    #[inline(always)]
    #[must_use]
    fn node_children(&self, node: NodeIndex) -> hierarchy::Children<'_> {
        self.hierarchy().children(node)
    }

    /// Get the next sibling of a node in the hierarchy.
    #[inline(always)]
    #[must_use]
    fn node_next_sibling(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.hierarchy().next(node)
    }

    /// Get the previous sibling of a node in the hierarchy.
    #[inline(always)]
    #[must_use]
    fn node_prev_sibling(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.hierarchy().prev(node)
    }
}

/// Main weighted graph interface, mutable operations.
pub trait GraphMut<'a, N = (), P = ()>: Graph<'a, N, P>
where
    N: 'a + Clone,
    P: 'a + Clone,
{
    /// Returns mutable references to the underlying components.
    #[must_use]
    fn components_mut<'b, 'u, 'w, 'h>(
        &'b mut self,
    ) -> (
        &'u mut UnweightedGraph,
        &'w mut Weights<N, P>,
        &'h mut Hierarchy,
    )
    where
        'b: 'u + 'w + 'h;

    /// Returns a mutable reference to the underlying unweighted graph.
    #[must_use]
    fn unweighted_mut(&mut self) -> &mut UnweightedGraph {
        self.components_mut().0
    }

    /// Returns a mutable reference to the weight component.
    #[must_use]
    fn weights_mut(&mut self) -> &mut Weights<N, P> {
        self.components_mut().1
    }

    /// Returns a mutable reference to the hierarchy component.
    #[must_use]
    fn hierarchy_mut(&mut self) -> &mut Hierarchy {
        self.components_mut().2
    }

    /// Get the weight of a given node.
    #[inline(always)]
    #[must_use]
    fn node_weight_mut(&'a mut self, node: NodeIndex) -> Option<&'a mut N> {
        self.weights_mut().try_get_node_mut(node)
    }

    /// Set the weight of a given node.
    #[inline(always)]
    fn set_node_weight(&mut self, node: NodeIndex, weight: N) {
        self.weights_mut().set_node(node, weight);
    }

    /// Get the weight of a given port.
    #[inline(always)]
    #[must_use]
    fn port_weight_mut(&'a mut self, port: PortIndex) -> Option<&'a mut P> {
        self.weights_mut().try_get_port_mut(port)
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
    /// # use portgraph::{PortGraph, GraphMut, Graph};
    /// let mut g = PortGraph::<(),()>::new();
    /// let node = g.add_node((), 4, 3);
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
    /// # use portgraph::{PortGraph, GraphMut, Graph};
    /// let mut g = PortGraph::<(),()>::new();
    /// let node = g.add_node((), 4, 3);
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
    /// # use portgraph::{PortGraph, GraphMut, Graph};
    /// let mut g = PortGraph::<(),()>::new();
    /// let node = g.add_node((), 4, 3);
    /// //g.resize_ports(node, 5, 2); # TODO: implement
    /// //assert_eq!(g.inputs(node).count(), 5);
    /// //assert_eq!(g.outputs(node).count(), 2);
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

    /// Link two nodes at an input and output port offset.
    fn link_nodes(
        &mut self,
        from: NodeIndex,
        from_offset: usize,
        to: NodeIndex,
        to_offset: usize,
    ) -> Result<(PortIndex, PortIndex), LinkError> {
        // TODO: The LinkError thrown when the offset is invalid requires a PortIndex, so we are forced to create (an invalid) one from the offset.
        let from_port = self
            .output(from, from_offset)
            .ok_or(LinkError::UnknownPort(PortIndex::new(from_offset)))?;
        let to_port = self
            .input(to, to_offset)
            .ok_or(LinkError::UnknownPort(PortIndex::new(to_offset)))?;
        self.unweighted_mut().link_ports(from_port, to_port)?;
        Ok((from_port, to_port))
    }

    /// Unlinks the `port` and returns the port it was linked to. Returns `None`
    /// when the port was not linked.
    #[inline(always)]
    fn unlink_port(&mut self, port: PortIndex) -> Option<PortIndex> {
        self.unweighted_mut().unlink_port(port)
    }

    /// Insert another graph into this graph.
    ///
    /// Every time a node or port is inserted, the rekey function will be called with its old and new index.
    fn insert_graph<G, FN, FP>(&mut self, mut _other: G, mut _rekey_nodes: FN, mut _rekey_ports: FP)
    where
        G: Graph<'a, N, P> + Sized,
        FN: FnMut(NodeIndex, NodeIndex),
        FP: FnMut(PortIndex, PortIndex),
    {
        todo!("Insert graph in unweighted, with a callback to rekey the weights and hierarchy")
    }

    /// Compacts the storage of nodes in the graph so that all nodes are stored consecutively.
    ///
    /// Every time a node is moved, the `rekey` function will be called with its old and new index.
    #[inline(always)]
    fn compact_nodes(&mut self, mut rekey: impl FnMut(NodeIndex, NodeIndex)) {
        let (unweighted, weights, hierarchy) = self.components_mut();
        unweighted.compact_nodes(|old, new| {
            rekey(old, new);
            weights.rekey_node(old, new);
            hierarchy.rekey(old, new);
        });
    }

    /// Compacts the storage of ports in the graph so that all ports are stored consecutively.
    ///
    /// Every time a port is moved, the `rekey` function will be called with its old and new index.
    #[inline(always)]
    fn compact_ports(&mut self, mut rekey: impl FnMut(PortIndex, PortIndex)) {
        let (unweighted, weights, _) = self.components_mut();
        unweighted.compact_ports(|old, new| {
            rekey(old, new);
            weights.rekey_port(old, new);
        });
    }

    /// Iterate over the node weights of a graph.
    fn node_weights_mut(&'a mut self) -> iter::Empty<(NodeIndex, &'a mut N)> {
        todo!()
    }

    /// Iterate over the port weights of a graph.
    fn port_weights_mut(&'a mut self) -> iter::Empty<(PortIndex, &'a mut N)> {
        todo!()
    }
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

    fn weights(&self) -> &Weights<N, P> {
        &self.weights
    }

    fn hierarchy(&self) -> &Hierarchy {
        &self.hierarchy
    }
}

impl<'a, N, P> GraphMut<'a, N, P> for PortGraph<N, P>
where
    N: 'a + Clone,
    P: 'a + Clone,
{
    fn components_mut<'b, 'u, 'w, 'h>(
        &'b mut self,
    ) -> (
        &'u mut UnweightedGraph,
        &'w mut Weights<N, P>,
        &'h mut Hierarchy,
    )
    where
        'b: 'u + 'w + 'h,
    {
        (&mut self.unweighted, &mut self.weights, &mut self.hierarchy)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    #[test]
    fn empty() {
        let graph: PortGraph<usize, usize> = PortGraph::new();
        assert_eq!(graph.node_count(), 0);
        assert_eq!(graph.port_count(), 0);
        assert!(graph.nodes_iter().next().is_none());
        assert!(graph.ports_iter().next().is_none());
    }

    #[test]
    #[ignore = "unimplemented methods"]
    fn test_insert_graph() {
        let mut g = PortGraph::<i8, i8>::with_capacity(3, 2);

        let n0 = g.add_node(0, 0, 1);
        let n1 = g.add_node_with_ports(1, vec![-1], vec![-2]);
        let n2 = g.add_node(2, 1, 0);

        let p0out = g.output(n0, 0).unwrap();
        let p1in = g.input(n1, 0).unwrap();
        let p1out = g.output(n1, 0).unwrap();
        let p2in = g.input(n2, 0).unwrap();

        g.link_ports(p0out, p1in).unwrap();
        g.link_ports(p1out, p2in).unwrap();

        let mut g2 = PortGraph::<i8, i8>::with_capacity(2, 1);

        let n3 = g2.add_node(3, 0, 1);
        let n4 = g2.add_node_with_ports(4, vec![-3], vec![]);

        let p3out = g2.outputs(n3).next().unwrap();
        let p4in = g2.inputs(n4).next().unwrap();
        g2.link_ports(p3out, p4in).unwrap();

        let mut node_map = HashMap::new();
        let mut port_map = HashMap::new();
        g.insert_graph(
            g2,
            |old, new| {
                node_map.insert(old, new);
            },
            |old, new| {
                port_map.insert(old, new);
            },
        );

        assert_eq!(g.node_count(), 5);
        assert_eq!(g.port_count(), 6);
        assert_eq!(g.edge_count(), 3);

        // Check nodes and node weights
        for (weight, n) in [n0, n1, n2].iter().enumerate() {
            assert!(!node_map.contains_key(n));
            assert!(g.contains_node(*n));
            assert_eq!(g.node_weight(*n), Some(&(weight as i8)));
        }
        for (weight, n) in [n3, n4].iter().enumerate() {
            let weight = weight + 3;
            assert!(node_map.contains_key(n));
            let n = node_map[n];
            assert!(g.contains_node(n));
            assert_eq!(g.node_weight(n), Some(&(weight as i8)));
        }

        // Check ports and port weights
        for p in [p0out, p1in, p1out, p2in] {
            assert!(!port_map.contains_key(&p));
            assert!(g.contains_port(p));
        }
        for p in [p3out, p4in] {
            assert!(port_map.contains_key(&p));
            let p = port_map[&p];
            assert!(g.contains_port(p));
        }
        assert_eq!(g.port_weight(p1in), Some(&-1));
        assert_eq!(g.port_weight(p1out), Some(&-2));
        assert_eq!(g.port_weight(port_map[&p4in]), Some(&-3));

        // Check links
        assert_eq!(g.port_link(p0out), Some(p1in));
        assert_eq!(g.port_link(p1out), Some(p2in));
        assert_eq!(g.port_link(port_map[&p3out]), Some(port_map[&p4in]));
    }

    #[test]
    #[ignore = "unimplemented methods"]
    fn test_compact() {
        let mut g = PortGraph::<i8, i8>::with_capacity(3, 2);

        let n0 = g.add_node(0, 0, 2);
        let n1 = g.add_node(1, 1, 1);
        let n2 = g.add_node(2, 2, 0);

        assert_eq!(g.node_count(), 3);
        assert_eq!(g.port_count(), 6);
        assert_eq!(g.edge_count(), 0);

        g.link_ports(g.output(n0, 0).unwrap(), g.input(n1, 0).unwrap())
            .unwrap();

        g.link_ports(g.output(n1, 0).unwrap(), g.input(n2, 0).unwrap())
            .unwrap();

        let p0 = g.output(n0, 1).unwrap();
        let p2 = g.input(n2, 1).unwrap();
        g.link_ports(p0, p2).unwrap();

        assert_eq!(g.node_count(), 3);
        assert_eq!(g.port_count(), 6);
        assert_eq!(g.edge_count(), 3);

        assert_eq!(g.remove_node(n1), Some(1));

        assert_eq!(g.node_count(), 2);
        assert_eq!(g.port_count(), 2);
        assert_eq!(g.edge_count(), 1);

        let mut node_map: HashMap<NodeIndex, NodeIndex> = HashMap::new();
        let mut port_map: HashMap<PortIndex, PortIndex> = HashMap::new();
        g.compact_nodes(|old: NodeIndex, new: NodeIndex| {
            node_map.insert(old, new);
        });
        g.compact_ports(|old, new| {
            port_map.insert(old, new);
        });

        assert_eq!(g.node_count(), 2);
        assert_eq!(g.port_count(), 2);
        assert_eq!(g.edge_count(), 1);

        assert!(!node_map.contains_key(&n1));
        assert_eq!(g.node_weight(node_map[&n0]), Some(&0));
        assert_eq!(g.node_weight(node_map[&n2]), Some(&2));

        assert_eq!(
            g.connected(node_map[&n0], node_map[&n2]),
            Some((port_map[&p0], port_map[&p2]))
        );
    }
}
