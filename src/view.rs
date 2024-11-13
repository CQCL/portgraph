//! Abstractions over portgraph representations.

pub mod filter;
pub mod refs;
pub mod region;
pub mod subgraph;

#[cfg(feature = "petgraph")]
pub mod petgraph;

use std::collections::HashMap;

use crate::{portgraph::PortOperation, Direction, LinkError, NodeIndex, PortIndex, PortOffset};

pub use filter::{FilteredGraph, LinkFilter, NodeFilter, NodeFiltered};
pub use region::{FlatRegion, Region};
pub use subgraph::Subgraph;

/// Core capabilities for querying a graph containing nodes and ports.
pub trait PortView {
    /// Returns the direction of the `port`.
    #[must_use]
    fn port_direction(&self, port: impl Into<PortIndex>) -> Option<Direction>;

    /// Returns the node that the `port` belongs to.
    #[must_use]
    fn port_node(&self, port: impl Into<PortIndex>) -> Option<NodeIndex>;

    /// Returns the index of a `port` within its node's port list.
    #[must_use]
    fn port_offset(&self, port: impl Into<PortIndex>) -> Option<PortOffset>;

    /// Returns the port index for a given node, direction, and offset.
    #[must_use]
    fn port_index(&self, node: NodeIndex, offset: PortOffset) -> Option<PortIndex>;

    /// Iterates over all the ports of the `node` in the given `direction`.
    #[must_use]
    fn ports(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = PortIndex>;

    /// Iterates over the input and output ports of the `node` in sequence.
    #[must_use]
    fn all_ports(&self, node: NodeIndex) -> impl Iterator<Item = PortIndex>;

    /// Iterates over all the input ports of the `node`.
    ///
    /// Shorthand for [`PortView::ports`].
    #[must_use]
    #[inline]
    fn inputs(&self, node: NodeIndex) -> impl Iterator<Item = PortIndex> {
        self.ports(node, Direction::Incoming)
    }

    /// Iterates over all the output ports of the `node`.
    ///
    /// Shorthand for [`PortView::ports`].
    #[must_use]
    #[inline]
    fn outputs(&self, node: NodeIndex) -> impl Iterator<Item = PortIndex> {
        self.ports(node, Direction::Outgoing)
    }

    /// Returns the input port at the given offset in the `node`.
    ///
    /// Shorthand for [`PortView::port_index`].
    #[must_use]
    fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;

    /// Returns the output port at the given offset in the `node`.
    ///
    /// Shorthand for [`PortView::port_index`].
    #[must_use]
    fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;

    /// Returns the number of input ports of the `node`.
    ///
    /// Shorthand for [`PortView::num_ports`].
    #[must_use]
    #[inline]
    fn num_inputs(&self, node: NodeIndex) -> usize {
        self.num_ports(node, Direction::Incoming)
    }

    /// Returns the number of output ports of the `node`.
    ///
    /// Shorthand for [`PortView::num_ports`].
    #[must_use]
    #[inline]
    fn num_outputs(&self, node: NodeIndex) -> usize {
        self.num_ports(node, Direction::Outgoing)
    }

    /// Returns the number of ports of the `node` in the given `direction`.
    #[must_use]
    fn num_ports(&self, node: NodeIndex, direction: Direction) -> usize;

    /// Iterates over all the port offsets of the `node` in the given `direction`.
    ///
    /// # Example
    ///
    /// ```
    /// # use ::portgraph::*;
    /// let mut graph = PortGraph::new();
    /// let node = graph.add_node(0, 2);
    ///
    /// assert!(graph.links(node, Direction::Incoming).eq([]));
    /// assert!(graph.port_offsets(node, Direction::Outgoing).eq([PortOffset::new_outgoing(0), PortOffset::new_outgoing(1)]));
    /// ```
    #[must_use]
    fn port_offsets(
        &self,
        node: NodeIndex,
        direction: Direction,
    ) -> impl Iterator<Item = PortOffset>;

    /// Iterates over the input and output port offsets of the `node` in sequence.
    #[must_use]
    fn all_port_offsets(&self, node: NodeIndex) -> impl Iterator<Item = PortOffset>;

    /// Iterates over all the input port offsets of the `node`.
    ///
    /// Shorthand for [`PortView::port_offsets`].
    #[must_use]
    #[inline]
    fn input_offsets(&self, node: NodeIndex) -> impl Iterator<Item = PortOffset> {
        self.port_offsets(node, Direction::Incoming)
    }

    /// Iterates over all the output port offsets of the `node`.
    ///
    /// Shorthand for [`PortView::port_offsets`].
    #[must_use]
    #[inline]
    fn output_offsets(&self, node: NodeIndex) -> impl Iterator<Item = PortOffset> {
        self.port_offsets(node, Direction::Outgoing)
    }

    /// Returns whether the port graph contains the `node`.
    #[must_use]
    fn contains_node(&self, node: NodeIndex) -> bool;

    /// Returns whether the port graph contains the `port`.
    #[must_use]
    fn contains_port(&self, port: PortIndex) -> bool;

    /// Returns whether the port graph has no nodes nor ports.
    #[must_use]
    fn is_empty(&self) -> bool;

    /// Returns the number of nodes in the port graph.
    #[must_use]
    fn node_count(&self) -> usize;

    /// Returns the number of ports in the port graph.
    #[must_use]
    fn port_count(&self) -> usize;

    /// Iterates over the nodes in the port graph.
    #[must_use]
    fn nodes_iter(&self) -> impl Iterator<Item = NodeIndex>;

    /// Iterates over the ports in the port graph.
    #[must_use]
    fn ports_iter(&self) -> impl Iterator<Item = PortIndex>;

    /// Returns the capacity of the underlying buffer for nodes.
    #[must_use]
    fn node_capacity(&self) -> usize;

    /// Returns the capacity of the underlying buffer for ports.
    #[must_use]
    fn port_capacity(&self) -> usize;

    /// Returns the allocated port capacity for a specific node.
    ///
    /// Changes to the number of ports of the node will not reallocate
    /// until the number of ports exceeds this capacity.
    #[must_use]
    fn node_port_capacity(&self, node: NodeIndex) -> usize;
}

/// Core capabilities for mutating a graph containing nodes and ports.
pub trait PortMut: PortView {
    /// Adds a node to the portgraph with a given number of input and output ports.
    ///
    /// # Panics
    ///
    /// Panics if the total number of ports exceeds `u16::MAX`.
    ///
    /// # Example
    ///
    /// ```
    /// # use ::portgraph::*;
    /// let mut g = PortGraph::new();
    /// let node = g.add_node(4, 3);
    /// assert_eq!(g.inputs(node).count(), 4);
    /// assert_eq!(g.outputs(node).count(), 3);
    /// assert!(g.contains_node(node));
    /// ```
    fn add_node(&mut self, incoming: usize, outgoing: usize) -> NodeIndex;

    /// Remove a node from the port graph. All ports of the node will be
    /// unlinked and removed as well. Does nothing if the node does not exist.
    ///
    /// # Example
    ///
    /// ```
    /// # use ::portgraph::*;
    /// let mut g = PortGraph::new();
    /// let node0 = g.add_node(1, 1);
    /// let node1 = g.add_node(1, 1);
    /// let out0 = g.outputs(node0).nth(0).unwrap();
    /// let out1 = g.outputs(node1).nth(0).unwrap();
    /// let in0 = g.inputs(node0).nth(0).unwrap();
    /// let in1 = g.inputs(node1).nth(0).unwrap();
    /// g.link_ports(out0, in1);
    /// g.link_ports(out1, in0);
    /// g.remove_node(node0);
    /// assert!(!g.contains_node(node0));
    /// assert!(g.port_link(g.outputs(node1).nth(0).unwrap()).is_none());
    /// assert!(g.port_link(g.inputs(node1).nth(0).unwrap()).is_none());
    /// ```
    fn remove_node(&mut self, node: NodeIndex);

    /// Removes all nodes and ports from the port graph.
    fn clear(&mut self);

    /// Reserves enough capacity to insert at least the given number of additional nodes and ports.
    ///
    /// This method does not take into account the length of the free list and might overallocate speculatively.
    fn reserve(&mut self, nodes: usize, ports: usize);

    /// Changes the number of ports of the `node` to the given `incoming` and `outgoing` counts.
    ///
    /// Invalidates the indices of the node's ports. If the number of incoming or outgoing ports
    /// is reduced, the ports are removed from the end of the port list.
    ///
    /// Every time a port is moved, the `rekey` function will be called with its old and new index.
    /// If the port is removed, the new index will be `None`.
    ///
    /// This operation is O(n) where n is the number of ports of the node.
    fn set_num_ports<F>(&mut self, node: NodeIndex, incoming: usize, outgoing: usize, rekey: F)
    where
        F: FnMut(PortIndex, PortOperation);

    /// Swaps the indices of two nodes.
    fn swap_nodes(&mut self, a: NodeIndex, b: NodeIndex);

    /// Compacts the storage of nodes in the portgraph as much as possible. Note
    /// that node indices won't necessarily be consecutive after this process.
    ///
    /// Every time a node is moved, the `rekey` function will be called with its
    /// old and new index.
    fn compact_nodes<F>(&mut self, rekey: F)
    where
        F: FnMut(NodeIndex, NodeIndex);

    /// Compacts the storage of ports in the portgraph as much as possible. Note
    /// that indices won't necessarily be consecutive after this process.
    ///
    /// Every time a port is moved, the `rekey` function will be called with is
    /// old and new index.
    fn compact_ports<F>(&mut self, rekey: F)
    where
        F: FnMut(PortIndex, PortIndex);

    /// Shrinks the underlying buffers to the fit the data.
    ///
    /// This does not alter existing indices.
    fn shrink_to_fit(&mut self);
}

/// Operations pertaining the adjacency of nodes in a port graph.
pub trait LinkView: PortView {
    /// The identifier for the endpoints of a link.
    type LinkEndpoint: Into<PortIndex> + Copy;

    /// Returns an iterator over every pair of matching ports connecting `from`
    /// with `to`.
    ///
    /// # Example
    /// ```
    /// # use ::portgraph::*;
    /// let mut g = PortGraph::new();
    /// let a = g.add_node(0, 2);
    /// let b = g.add_node(2, 0);
    ///
    /// g.link_nodes(a, 0, b, 0).unwrap();
    /// g.link_nodes(a, 1, b, 1).unwrap();
    ///
    /// let mut connections = g.get_connections(a, b);
    /// assert_eq!(connections.next(), Some((g.output(a,0).unwrap(), g.input(b,0).unwrap())));
    /// assert_eq!(connections.next(), Some((g.output(a,1).unwrap(), g.input(b,1).unwrap())));
    /// assert_eq!(connections.next(), None);
    /// ```
    #[must_use]
    fn get_connections(
        &self,
        from: NodeIndex,
        to: NodeIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)>;

    /// Checks whether there is a directed link between the two nodes and
    /// returns the first matching pair of ports.
    ///
    /// # Example
    /// ```
    /// # use ::portgraph::*;
    /// let mut g = PortGraph::new();
    /// let a = g.add_node(0, 2);
    /// let b = g.add_node(2, 0);
    ///
    /// g.link_nodes(a, 0, b, 0).unwrap();
    /// g.link_nodes(a, 1, b, 1).unwrap();
    ///
    /// assert_eq!(g.get_connection(a, b), Some((g.output(a,0).unwrap(), g.input(b,0).unwrap())));
    /// ```
    #[must_use]
    fn get_connection(
        &self,
        from: NodeIndex,
        to: NodeIndex,
    ) -> Option<(Self::LinkEndpoint, Self::LinkEndpoint)> {
        self.get_connections(from, to).next()
    }

    /// Checks whether there is a directed link between the two nodes.
    ///
    /// # Example
    /// ```
    /// # use ::portgraph::*;
    /// let mut g = PortGraph::new();
    /// let a = g.add_node(0, 2);
    /// let b = g.add_node(2, 0);
    ///
    /// g.link_nodes(a, 0, b, 0).unwrap();
    ///
    /// assert!(g.connected(a, b));
    /// ```
    #[must_use]
    #[inline]
    fn connected(&self, from: NodeIndex, to: NodeIndex) -> bool {
        self.get_connection(from, to).is_some()
    }

    /// Returns the port that the given `port` is linked to.
    #[must_use]
    fn port_links(
        &self,
        port: PortIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)>;

    /// Return the link to the provided port, if not connected return None.
    /// If this port has multiple connected subports, an arbitrary one is returned.
    #[must_use]
    #[inline]
    fn port_link(&self, port: PortIndex) -> Option<Self::LinkEndpoint> {
        self.port_links(port).next().map(|(_, p)| p)
    }

    /// Iterates over the connected links of the `node` in the given
    /// `direction`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ::portgraph::*;
    ///
    /// let mut graph = PortGraph::new();
    ///
    /// let node_a = graph.add_node(0, 2);
    /// let node_b = graph.add_node(1, 0);
    ///
    /// let port_a = graph.outputs(node_a).next().unwrap();
    /// let port_b = graph.inputs(node_b).next().unwrap();
    ///
    /// graph.link_ports(port_a, port_b).unwrap();
    ///
    /// assert!(graph.links(node_a, Direction::Outgoing).eq([(port_a, port_b)]));
    /// assert!(graph.links(node_b, Direction::Incoming).eq([(port_b, port_a)]));
    /// ```
    #[must_use]
    fn links(
        &self,
        node: NodeIndex,
        direction: Direction,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)>;

    /// Iterates over the connected input and output links of the `node` in sequence.
    #[must_use]
    fn all_links(
        &self,
        node: NodeIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)>;

    /// Iterates over the connected input links of the `node`. Shorthand for
    /// [`LinkView::links`].
    #[must_use]
    #[inline]
    fn input_links(
        &self,
        node: NodeIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> {
        self.links(node, Direction::Incoming)
    }

    /// Iterates over the connected output links of the `node`. Shorthand for
    /// [`LinkView::links`].
    #[must_use]
    #[inline]
    fn output_links(
        &self,
        node: NodeIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> {
        self.links(node, Direction::Outgoing)
    }

    /// Iterates over neighbour nodes in the given `direction`.
    /// May contain duplicates if the graph has multiple links between nodes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ::portgraph::*;
    ///
    /// let mut graph = PortGraph::new();
    ///
    /// let a = graph.add_node(0, 1);
    /// let b = graph.add_node(2, 1);
    ///
    /// graph.link_nodes(a, 0, b, 0).unwrap();
    /// graph.link_nodes(b, 0, b, 1).unwrap();
    ///
    /// assert!(graph.neighbours(a, Direction::Outgoing).eq([b]));
    /// assert!(graph.neighbours(b, Direction::Incoming).eq([a,b]));
    /// ```
    #[must_use]
    fn neighbours(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = NodeIndex>;

    /// Iterates over the input and output neighbours of the `node` in sequence.
    #[must_use]
    fn all_neighbours(&self, node: NodeIndex) -> impl Iterator<Item = NodeIndex>;

    /// Iterates over the input neighbours of the `node`. Shorthand for [`LinkView::neighbours`].
    #[must_use]
    #[inline]
    fn input_neighbours(&self, node: NodeIndex) -> impl Iterator<Item = NodeIndex> {
        self.neighbours(node, Direction::Incoming)
    }

    /// Iterates over the output neighbours of the `node`. Shorthand for [`LinkView::neighbours`].
    #[must_use]
    #[inline]
    fn output_neighbours(&self, node: NodeIndex) -> impl Iterator<Item = NodeIndex> {
        self.neighbours(node, Direction::Outgoing)
    }

    /// Returns the number of links between ports.
    #[must_use]
    fn link_count(&self) -> usize;
}

/// Mutating operations pertaining the adjacency of nodes in a port graph.
pub trait LinkMut: LinkView + PortMut {
    /// Link an output port to an input port.
    ///
    /// # Example
    ///
    /// ```
    /// # use ::portgraph::*;
    /// let mut g = PortGraph::new();
    /// let node0 = g.add_node(0, 1);
    /// let node1 = g.add_node(1, 0);
    /// let node0_output = g.output(node0, 0).unwrap();
    /// let node1_input = g.input(node1, 0).unwrap();
    /// g.link_ports(node0_output, node1_input).unwrap();
    /// assert_eq!(g.port_link(node0_output), Some(node1_input));
    /// assert_eq!(g.port_link(node1_input), Some(node0_output));
    /// ```
    ///
    /// # Errors
    ///
    ///  - If `port_a` or `port_b` does not exist.
    ///  - If `port_a` and `port_b` have the same direction.
    fn link_ports(
        &mut self,
        port_a: PortIndex,
        port_b: PortIndex,
    ) -> Result<(Self::LinkEndpoint, Self::LinkEndpoint), LinkError>;

    /// Links two nodes at an input and output port offsets.
    ///
    /// # Errors
    ///
    ///  - If the ports and nodes do not exist.
    fn link_nodes(
        &mut self,
        from: NodeIndex,
        from_output: usize,
        to: NodeIndex,
        to_input: usize,
    ) -> Result<(Self::LinkEndpoint, Self::LinkEndpoint), LinkError> {
        self.link_offsets(
            from,
            PortOffset::new_outgoing(from_output),
            to,
            PortOffset::new_incoming(to_input),
        )
    }

    /// Links two nodes at an input and output port offsets.
    ///
    /// # Errors
    ///
    ///  - If the ports and nodes do not exist.
    ///  - If the ports have the same direction.
    fn link_offsets(
        &mut self,
        node_a: NodeIndex,
        offset_a: PortOffset,
        node_b: NodeIndex,
        offset_b: PortOffset,
    ) -> Result<(Self::LinkEndpoint, Self::LinkEndpoint), LinkError> {
        let from_port = self
            .port_index(node_a, offset_a)
            .ok_or(LinkError::UnknownOffset {
                node: node_a,
                offset: offset_a,
            })?;
        let to_port = self
            .port_index(node_b, offset_b)
            .ok_or(LinkError::UnknownOffset {
                node: node_b,
                offset: offset_b,
            })?;
        self.link_ports(from_port, to_port)
    }

    /// Unlinks all connections to the `port`. If the port was connected,
    /// returns one of the ports it was connected to.
    fn unlink_port(&mut self, port: PortIndex) -> Option<Self::LinkEndpoint>;

    /// Inserts another graph into this graph.
    ///
    /// Returns a map from the old node indices to the new node indices.
    fn insert_graph(
        &mut self,
        other: &impl LinkView,
    ) -> Result<HashMap<NodeIndex, NodeIndex>, LinkError> {
        self.reserve(other.node_count(), other.port_count());
        let mut rekeys = HashMap::with_capacity(other.node_count());
        for old in other.nodes_iter() {
            let new = self.add_node(other.num_inputs(old), other.num_outputs(old));
            rekeys.insert(old, new);
            for (from, to) in other.all_links(old) {
                // If the other node has already been inserted, we can link
                let Some(&other_node) = rekeys.get(&other.port_node(to).unwrap()) else {
                    continue;
                };
                self.link_offsets(
                    new,
                    other.port_offset(from).unwrap(),
                    other_node,
                    other.port_offset(to).unwrap(),
                )?;
            }
        }
        Ok(rekeys)
    }
}

/// Abstraction over a portgraph that may have multiple connections per node.
pub trait MultiView: LinkView {
    /// Return the subport linked to the given `port`. If the port is not
    /// connected, return None.
    #[must_use]
    fn subport_link(&self, subport: Self::LinkEndpoint) -> Option<Self::LinkEndpoint>;

    /// Iterates over all the subports of the `node` in the given `direction`.
    #[must_use]
    fn subports(
        &self,
        node: NodeIndex,
        direction: Direction,
    ) -> impl Iterator<Item = Self::LinkEndpoint>;

    /// Iterates over the input and output subports of the `node` in sequence.
    #[must_use]
    fn all_subports(&self, node: NodeIndex) -> impl Iterator<Item = Self::LinkEndpoint>;

    /// Iterates over all the input subports of the `node`.
    ///
    /// Shorthand for [`MultiView::subports`].
    #[must_use]
    #[inline]
    fn subport_inputs(&self, node: NodeIndex) -> impl Iterator<Item = Self::LinkEndpoint> {
        self.subports(node, Direction::Incoming)
    }

    /// Iterates over all the output subports of the `node`.
    ///
    /// Shorthand for [`MultiView::subports`].
    #[must_use]
    #[inline]
    fn subport_outputs(&self, node: NodeIndex) -> impl Iterator<Item = Self::LinkEndpoint> {
        self.subports(node, Direction::Outgoing)
    }
}

/// Abstraction for mutating a portgraph that may have multiple connections per node.
pub trait MultiMut: MultiView + LinkMut {
    /// Link an output subport to an input subport.
    ///
    /// # Errors
    ///
    ///  - If `subport_from` or `subport_to` does not exist.
    ///  - If `subport_a` and `subport_b` have the same direction.
    ///  - If `subport_from` or `subport_to` is already linked.
    fn link_subports(
        &mut self,
        subport_from: Self::LinkEndpoint,
        subport_to: Self::LinkEndpoint,
    ) -> Result<(), LinkError>;

    /// Unlinks the `port` and returns the subport it was linked to. Returns `None`
    /// when the port was not linked.
    fn unlink_subport(&mut self, subport: Self::LinkEndpoint) -> Option<Self::LinkEndpoint>;
}
