//! Wrapper around a portgraph providing multiports via implicit copy nodes.

mod iter;

pub use self::iter::{
    Neighbours, NodeConnections, NodeLinks, NodeSubports, Nodes, PortLinks, Ports,
};
use crate::portgraph::{NodePortOffsets, NodePorts, PortOperation};
use crate::view::{LinkMut, MultiMut, MultiView, PortMut};
use crate::{
    Direction, LinkError, LinkView, NodeIndex, PortGraph, PortIndex, PortOffset, PortView,
    SecondaryMap,
};

use bitvec::vec::BitVec;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// An unlabelled port graph that allows multiple links to the same ports.
///
/// A port graph consists of a collection of nodes identified by a [`NodeIndex`].
/// Each node has an ordered sequence of input and output ports, identified by a [`PortIndex`] that is unique within the graph.
/// To optimize for the most common use case, the number of input and output ports of a node must be specified when the node is created.
/// Multiple connections to the same [`PortIndex`] can be distinguished by their [`SubportIndex`].
///
/// When a node and its associated ports are removed their indices will be reused on a best effort basis
/// when a new node is added.
/// The indices of unaffected nodes and ports remain stable.
#[derive(Clone, PartialEq, Default, Debug)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct MultiPortGraph {
    graph: PortGraph,
    /// Flags marking the internal ports of a multiport. That is, the ports connecting the main node and the copy nodes.
    multiport: BitVec,
    /// Flags marking the implicit copy nodes.
    copy_node: BitVec,
    /// Number of implicit copy nodes.
    copy_node_count: usize,
    /// Number of subports in the copy nodes of the graph.
    subport_count: usize,
}

/// Index of a multi port within a `MultiPortGraph`.
///
/// Note that the offsets of the subport indices are not guaranteed to be
/// contiguous nor well-ordered. They are not invalidated by adding or removing
/// other links to the same port.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct SubportIndex {
    port: PortIndex,
    subport_offset: u16,
}

impl MultiPortGraph {
    /// Create a new empty [`MultiPortGraph`].
    pub fn new() -> Self {
        Self {
            graph: PortGraph::new(),
            multiport: BitVec::new(),
            copy_node: BitVec::new(),
            copy_node_count: 0,
            subport_count: 0,
        }
    }

    /// Create a new empty [`MultiPortGraph`] with preallocated capacity.
    pub fn with_capacity(nodes: usize, ports: usize) -> Self {
        Self {
            graph: PortGraph::with_capacity(nodes, ports),
            multiport: BitVec::with_capacity(ports),
            copy_node: BitVec::with_capacity(nodes),
            copy_node_count: 0,
            subport_count: 0,
        }
    }

    /// Returns a reference to the internal plain portgraph.
    ///
    /// This graph exposes the copy nodes as well as the main nodes.
    pub fn as_portgraph(&self) -> &PortGraph {
        // Return the internal graph, exposing the copy nodes
        &self.graph
    }

    /// Given a node in the underlying flat portgraph, returns the main node for it.
    ///
    /// If the node is not a copy node, returns the node itself.
    pub fn pg_main_node(&self, node: NodeIndex) -> NodeIndex {
        if !self.copy_node.get(node) {
            return node;
        }
        self.port_node(self.copy_node_main_port(node).unwrap())
            .unwrap()
    }
}

impl PortView for MultiPortGraph {
    type Nodes<'a> = Nodes<'a>
    where
        Self: 'a;

    type Ports<'a> = Ports<'a>
    where
        Self: 'a;

    type NodePorts<'a> = NodePorts
    where
        Self: 'a;

    type NodePortOffsets<'a> = NodePortOffsets
    where
        Self: 'a;

    #[inline]
    fn port_direction(&self, port: impl Into<PortIndex>) -> Option<Direction> {
        self.graph.port_direction(port.into())
    }

    #[inline]
    fn port_node(&self, port: impl Into<PortIndex>) -> Option<NodeIndex> {
        self.graph.port_node(port.into())
    }

    #[inline]
    fn port_offset(&self, port: impl Into<PortIndex>) -> Option<PortOffset> {
        self.graph.port_offset(port.into())
    }

    #[inline]
    fn port_index(&self, node: NodeIndex, offset: PortOffset) -> Option<PortIndex> {
        self.graph.port_index(node, offset)
    }

    #[inline]
    fn ports(&self, node: NodeIndex, direction: Direction) -> Self::NodePorts<'_> {
        self.graph.ports(node, direction)
    }

    #[inline]
    fn all_ports(&self, node: NodeIndex) -> Self::NodePorts<'_> {
        self.graph.all_ports(node)
    }

    #[inline]
    fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.graph.input(node, offset)
    }

    #[inline]
    fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.graph.output(node, offset)
    }

    #[inline]
    fn num_ports(&self, node: NodeIndex, direction: Direction) -> usize {
        self.graph.num_ports(node, direction)
    }

    #[inline]
    fn port_offsets(&self, node: NodeIndex, direction: Direction) -> Self::NodePortOffsets<'_> {
        self.graph.port_offsets(node, direction)
    }

    #[inline]
    fn all_port_offsets(&self, node: NodeIndex) -> Self::NodePortOffsets<'_> {
        self.graph.all_port_offsets(node)
    }

    #[inline]
    fn contains_node(&self, node: NodeIndex) -> bool {
        self.graph.contains_node(node) && !self.copy_node.get(node)
    }

    #[inline]
    fn contains_port(&self, port: PortIndex) -> bool {
        self.graph
            .port_node(port)
            .map_or(false, |node| !self.copy_node.get(node))
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.node_count() == 0
    }

    #[inline]
    fn node_count(&self) -> usize {
        self.graph.node_count() - self.copy_node_count
    }

    #[inline]
    fn port_count(&self) -> usize {
        // Do not count the ports in the copy nodes. We have to subtract one of
        // the two ports connecting the copy nodes with their main nodes, in
        // addition to all the subports.
        self.graph.port_count() - self.subport_count - self.copy_node_count
    }
    #[inline]
    fn nodes_iter(&self) -> Self::Nodes<'_> {
        self::iter::Nodes {
            multigraph: self,
            iter: self.graph.nodes_iter(),
            len: self.node_count(),
        }
    }

    #[inline]
    fn ports_iter(&self) -> Self::Ports<'_> {
        Ports::new(self, self.graph.ports_iter())
    }

    #[inline]
    fn node_capacity(&self) -> usize {
        self.graph.node_capacity() - self.copy_node_count
    }

    #[inline]
    fn port_capacity(&self) -> usize {
        // See [`MultiPortGraph::port_count`]
        self.graph.port_capacity() - self.subport_count - self.copy_node_count
    }

    #[inline]
    fn node_port_capacity(&self, node: NodeIndex) -> usize {
        self.graph.node_port_capacity(node)
    }
}

impl PortMut for MultiPortGraph {
    #[inline]
    fn add_node(&mut self, incoming: usize, outgoing: usize) -> NodeIndex {
        self.graph.add_node(incoming, outgoing)
    }

    fn remove_node(&mut self, node: NodeIndex) {
        debug_assert!(!self.copy_node.get(node));
        for port in self.graph.all_ports(node) {
            if *self.multiport.get(port) {
                self.unlink_port(port);
            }
        }
        self.graph.remove_node(node);
    }

    fn clear(&mut self) {
        self.graph.clear();
        self.multiport.clear();
        self.copy_node.clear();
        self.copy_node_count = 0;
        self.subport_count = 0;
    }

    #[inline]
    fn reserve(&mut self, nodes: usize, ports: usize) {
        self.graph.reserve(nodes, ports);
        self.multiport.reserve(ports);
        self.copy_node.reserve(nodes);
    }

    fn set_num_ports<F>(&mut self, node: NodeIndex, incoming: usize, outgoing: usize, mut rekey: F)
    where
        F: FnMut(PortIndex, PortOperation),
    {
        let mut dropped_ports = Vec::new();
        let rekey_wrapper = |port, op| {
            match op {
                PortOperation::Removed { old_link } => dropped_ports.push((port, old_link)),
                PortOperation::Moved { new_index } => self.multiport.swap(port, new_index),
            }
            rekey(port, op);
        };
        self.graph
            .set_num_ports(node, incoming, outgoing, rekey_wrapper);
        for (port, old_link) in dropped_ports {
            if self.is_multiport(port) {
                let link = old_link.expect("Multiport node has no link");
                self.remove_copy_node(port, link);
            }
        }
    }

    fn compact_nodes<F>(&mut self, mut rekey: F)
    where
        F: FnMut(NodeIndex, NodeIndex),
    {
        self.graph.compact_nodes(|node, new_node| {
            self.copy_node.swap(node, new_node);
            rekey(node, new_node);
        });
    }

    fn compact_ports<F>(&mut self, mut rekey: F)
    where
        F: FnMut(PortIndex, PortIndex),
    {
        self.graph.compact_ports(|port, new_port| {
            self.multiport.swap(port, new_port);
            rekey(port, new_port);
        });
    }

    fn shrink_to_fit(&mut self) {
        self.graph.shrink_to_fit();
        self.multiport.shrink_to_fit();
        self.copy_node.shrink_to_fit();
    }
}

impl LinkView for MultiPortGraph {
    type LinkEndpoint = SubportIndex;

    type Neighbours<'a> = Neighbours<'a>
    where
        Self: 'a;

    type NodeConnections<'a> = NodeConnections<'a>
    where
        Self: 'a;

    type NodeLinks<'a> = NodeLinks<'a>
    where
        Self: 'a;

    type PortLinks<'a> = PortLinks<'a>
    where
        Self: 'a;

    #[inline]
    fn get_connections(&self, from: NodeIndex, to: NodeIndex) -> Self::NodeConnections<'_> {
        NodeConnections::new(self, to, self.output_links(from))
    }

    #[inline]
    fn port_links(&self, port: PortIndex) -> Self::PortLinks<'_> {
        PortLinks::new(self, port)
    }

    #[inline]
    fn links(&self, node: NodeIndex, direction: Direction) -> Self::NodeLinks<'_> {
        NodeLinks::new(self, self.ports(node, direction))
    }

    #[inline]
    fn all_links(&self, node: NodeIndex) -> Self::NodeLinks<'_> {
        NodeLinks::new(self, self.all_ports(node))
    }

    #[inline]
    fn neighbours(&self, node: NodeIndex, direction: Direction) -> Self::Neighbours<'_> {
        Neighbours::new(self, self.subports(node, direction))
    }

    #[inline]
    fn all_neighbours(&self, node: NodeIndex) -> Self::Neighbours<'_> {
        Neighbours::new(self, self.all_subports(node))
    }

    #[inline]
    fn link_count(&self) -> usize {
        // Do not count the links between copy nodes and their main nodes.
        self.graph.link_count() - self.copy_node_count
    }
}

impl LinkMut for MultiPortGraph {
    fn link_ports(
        &mut self,
        port_a: PortIndex,
        port_b: PortIndex,
    ) -> Result<(SubportIndex, SubportIndex), LinkError> {
        let (multiport_a, index_a) = self.get_free_multiport(port_a)?;
        let (multiport_b, index_b) = self.get_free_multiport(port_b)?;
        self.graph.link_ports(index_a, index_b)?;
        Ok((multiport_a, multiport_b))
    }

    fn unlink_port(&mut self, port: PortIndex) -> Option<SubportIndex> {
        if self.is_multiport(port) {
            let link = self
                .graph
                .port_link(port)
                .expect("MultiPortGraph error: a port marked as multiport has no link.");
            self.remove_copy_node(port, link)
        } else {
            self.graph.unlink_port(port).map(SubportIndex::new_unique)
        }
    }
}

impl MultiView for MultiPortGraph {
    type SubportIndex = SubportIndex;

    type NodeSubports<'a> = NodeSubports<'a>
    where
        Self: 'a;

    fn subport_link(&self, subport: Self::SubportIndex) -> Option<Self::SubportIndex> {
        let subport_index = self.get_subport_index(subport)?;
        let link = self.graph.port_link(subport_index)?;
        self.get_subport_from_index(link)
    }

    #[inline]
    fn subports(&self, node: NodeIndex, direction: Direction) -> Self::NodeSubports<'_> {
        NodeSubports::new(self, self.graph.ports(node, direction))
    }

    #[inline]
    fn all_subports(&self, node: NodeIndex) -> Self::NodeSubports<'_> {
        NodeSubports::new(self, self.graph.all_ports(node))
    }
}

impl MultiMut for MultiPortGraph {
    fn link_subports(
        &mut self,
        subport_from: Self::SubportIndex,
        subport_to: Self::SubportIndex,
    ) -> Result<(), LinkError> {
        // TODO: Custom errors
        let from_index = self
            .get_subport_index(subport_from)
            .expect("subport_from does not exist");
        let to_index = self
            .get_subport_index(subport_to)
            .expect("subport_to does not exist");
        self.graph.link_ports(from_index, to_index)?;
        Ok(())
    }

    fn unlink_subport(&mut self, subport: Self::SubportIndex) -> Option<Self::SubportIndex> {
        // TODO: Remove copy nodes when they are no longer needed?
        let subport_index = self.get_subport_index(subport)?;
        let link = self.graph.unlink_port(subport_index)?;
        self.get_subport_from_index(link)
    }
}

/// Internal helper methods
impl MultiPortGraph {
    /// Remove an internal copy node.
    ///
    /// Returns one of the links, if the node was connected
    fn remove_copy_node(
        &mut self,
        main_node_port: PortIndex,
        copy_port: PortIndex,
    ) -> Option<SubportIndex> {
        let copy_node = self.graph.port_node(copy_port).unwrap();
        let dir = self.port_direction(copy_port).unwrap();
        debug_assert!(self.copy_node.get(copy_node));

        let link = self.graph.links(copy_node, dir).next();
        let link = link.map(|(_, tgt)| self.get_subport_from_index(tgt).unwrap());

        let mut subports = self.graph.ports(copy_node, dir.reverse());
        self.multiport.set(copy_port, false);
        self.multiport.set(main_node_port, false);
        self.copy_node.set(copy_node, false);
        self.graph.remove_node(copy_node);
        self.copy_node_count -= 1;
        self.subport_count -= subports.len();
        debug_assert!(subports.all(|port| !self.multiport.get(port.index())));

        link
    }

    /// Returns a free multiport for the given port, along with its
    /// portgraph-level port index. Allocates a new copy node if needed, and
    /// grows the number of copy ports as needed.
    fn get_free_multiport(
        &mut self,
        port: PortIndex,
    ) -> Result<(SubportIndex, PortIndex), LinkError> {
        let Some(dir) = self.graph.port_direction(port) else {
            return Err(LinkError::UnknownPort{port});
        };
        let multiport = *self.multiport.get(port.index());
        let link = self.graph.port_link(port);
        match (multiport, link) {
            (false, None) => {
                // Port is disconnected, no need to allocate a copy node.
                Ok((SubportIndex::new_unique(port), port))
            }
            (false, Some(link)) => {
                // Port is connected, allocate a copy node.
                let in_out_count = match dir {
                    Direction::Incoming => (2, 1),
                    Direction::Outgoing => (1, 2),
                };
                let copy_node = self.graph.add_node(in_out_count.0, in_out_count.1);
                self.copy_node.set(copy_node, true);
                self.copy_node_count += 1;
                self.subport_count += 2;

                let copy_port = self.graph.ports(copy_node, dir.reverse()).next().unwrap();
                let old_link = self
                    .graph
                    .port_index(copy_node, PortOffset::new(dir, 0))
                    .unwrap();
                let subport = self
                    .graph
                    .port_index(copy_node, PortOffset::new(dir, 1))
                    .unwrap();

                // Connect the copy node to the original node, and re-connect the old link.
                self.graph.unlink_port(port);
                self.link_ports_directed(port, copy_port, dir)?;
                self.link_ports_directed(old_link, link, dir)?;
                self.multiport.set(copy_port.index(), true);
                self.multiport.set(port.index(), true);

                let subport_offset = 1;
                Ok((SubportIndex::new_multi(port, subport_offset), subport))
            }
            (true, Some(link)) => {
                // Port is already connected to a copy node.
                let copy_node = self.graph.port_node(link).unwrap();
                // We try to reuse an existing disconnected subport, if any.
                for (subport_offset, subport) in self.graph.ports(copy_node, dir).enumerate() {
                    if self.graph.port_link(subport).is_none() {
                        return Ok((SubportIndex::new_multi(port, subport_offset), subport));
                    }
                }
                // No free subport, we need to allocate a new one.
                let subport_offset = self.graph.num_ports(copy_node, dir);
                let subport = self.add_port(copy_node, dir);
                self.subport_count += 1;
                Ok((SubportIndex::new_multi(port, subport_offset), subport))
            }
            (true, None) => {
                // Missing copy node
                // TODO: Write a new error for this
                panic!("Missing copy node")
            }
        }
    }

    /// Adds an extra port to a node, in the specified direction.
    #[inline]
    fn add_port(&mut self, node: NodeIndex, direction: Direction) -> PortIndex {
        let mut incoming = self.graph.num_inputs(node);
        let mut outgoing = self.graph.num_outputs(node);
        let new_offset = match direction {
            Direction::Incoming => {
                incoming += 1;
                incoming - 1
            }
            Direction::Outgoing => {
                outgoing += 1;
                outgoing - 1
            }
        };
        self.set_num_ports(node, incoming, outgoing, |_, _| {});
        self.graph
            .port_index(node, PortOffset::new(direction, new_offset))
            .unwrap()
    }

    /// Link two ports, using the direction of `port1` to determine the link.
    ///
    /// Avoids the `UnexpectedDirection` error when passing the ports in the wrong order.
    #[inline]
    fn link_ports_directed(
        &mut self,
        port1: PortIndex,
        port2: PortIndex,
        dir: Direction,
    ) -> Result<(), LinkError> {
        match dir {
            Direction::Incoming => self.graph.link_ports(port2, port1)?,
            Direction::Outgoing => self.graph.link_ports(port1, port2)?,
        };
        Ok(())
    }

    /// Returns the PortIndex from the main node that connects to this copy node.
    fn copy_node_main_port(&self, copy_node: NodeIndex) -> Option<PortIndex> {
        debug_assert!(self.copy_node.get(copy_node));
        let mut incoming = self.graph.inputs(copy_node);
        let mut outgoing = self.graph.outputs(copy_node);

        let internal_copy_port = match (incoming.len(), outgoing.len()) {
            (1, 1) => {
                // Copy node has one input and one output, we have to check the
                // `multiport` flag to determine on which direction is the main
                // node.
                let in_port = incoming.next().unwrap();
                let out_port = outgoing.next().unwrap();
                match self.multiport.get(in_port) {
                    true => in_port,
                    false => out_port,
                }
            }
            (1, _) => {
                // This is a copy node for an outgoing port.
                incoming.next().unwrap()
            }
            (_, 1) => {
                // This is a copy node for an incoming port.
                outgoing.next().unwrap()
            }
            _ => {
                // TODO: MultiGraph error
                panic!("A copy must have a single port connecting it to the main node. The node had {} inputs and {} outputs",
                    incoming.len(),
                    outgoing.len()
                )
            }
        };
        self.graph.port_link(internal_copy_port)
    }

    /// Returns whether the port is marked as multiport.
    ///
    /// That is, this port is part of the connection between a main port and a copy node.
    #[inline]
    fn is_multiport(&self, port: PortIndex) -> bool {
        *self.multiport.get(port)
    }

    /// Returns whether the node is a copy node.
    #[inline]
    fn is_copy_node(&self, node: NodeIndex) -> bool {
        *self.copy_node.get(node)
    }

    /// Get the copy node for a multiport PortIndex, if it exists.
    #[inline]
    fn get_copy_node(&self, port_index: PortIndex) -> Option<NodeIndex> {
        let link = self.graph.port_link(port_index)?;
        self.graph.port_node(link)
    }

    /// Get the `PortIndex` in the copy node for a SubportIndex.
    ///
    /// If the port is not a multiport, returns the port index in the operation node.
    fn get_subport_index(&self, subport: SubportIndex) -> Option<PortIndex> {
        let port_index = subport.port();
        if self.is_multiport(port_index) {
            let copy_node = self.get_copy_node(port_index)?;
            let dir = self.graph.port_direction(port_index)?;
            let subport_offset = PortOffset::new(dir, subport.offset());
            self.graph.port_index(copy_node, subport_offset)
        } else {
            Some(port_index)
        }
    }

    /// Checks if the given `PortIndex` corresponds to a subport, and computes the correct `SubportIndex`.
    /// This should be the inverse of `get_subport_index`.
    fn get_subport_from_index(&self, index: PortIndex) -> Option<SubportIndex> {
        let linked_node = self.graph.port_node(index).unwrap();
        if self.is_copy_node(linked_node) {
            let port = self.copy_node_main_port(linked_node)?;
            let link_offset = self.graph.port_offset(index)?;
            Some(SubportIndex::new_multi(port, link_offset.index()))
        } else {
            Some(SubportIndex::new_unique(index))
        }
    }
}

impl From<PortGraph> for MultiPortGraph {
    fn from(graph: PortGraph) -> Self {
        let node_count = graph.node_count();
        let port_count = graph.port_count();
        Self {
            graph,
            multiport: BitVec::with_capacity(port_count),
            copy_node: BitVec::with_capacity(node_count),
            copy_node_count: 0,
            subport_count: 0,
        }
    }
}

impl From<MultiPortGraph> for PortGraph {
    fn from(multi: MultiPortGraph) -> Self {
        // Return the internal graph, exposing the copy nodes
        multi.graph
    }
}

impl SubportIndex {
    /// Creates a new multiport index for a port without a copy node.
    #[inline]
    pub fn new_unique(port: PortIndex) -> Self {
        Self {
            port,
            subport_offset: 0,
        }
    }

    /// Creates a new multiport index.
    ///
    /// # Panics
    ///
    /// If the subport index is more than 2^16.
    #[inline]
    pub fn new_multi(port: PortIndex, subport_offset: usize) -> Self {
        assert!(
            subport_offset < u16::MAX as usize,
            "Subport index too large"
        );
        Self {
            port,
            subport_offset: subport_offset as u16,
        }
    }

    /// Returns the port index.
    #[inline]
    pub fn port(self) -> PortIndex {
        self.port
    }

    /// Returns the offset of the subport.
    ///
    /// If the port is not a multiport, this will always return 0.
    #[inline]
    pub fn offset(self) -> usize {
        self.subport_offset as usize
    }
}

impl From<SubportIndex> for PortIndex {
    fn from(index: SubportIndex) -> Self {
        PortIndex::new(index.port.index())
    }
}

impl std::fmt::Debug for SubportIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SubportIndex({}:{})", self.port.index(), self.offset())
    }
}

#[cfg(test)]
pub mod test {
    use super::*;
    use itertools::Itertools;

    #[test]
    fn create_graph() {
        let graph = MultiPortGraph::new();

        assert_eq!(graph.node_count(), 0);
        assert_eq!(graph.port_count(), 0);
        assert_eq!(graph.link_count(), 0);
        assert_eq!(graph.nodes_iter().count(), 0);
        assert_eq!(graph.ports_iter().count(), 0);
    }

    #[test]
    fn link_ports() {
        let mut g = MultiPortGraph::new();
        let node0 = g.add_node(2, 1);
        let node1 = g.add_node(1, 2);
        let node0_output = g.output(node0, 0).unwrap();
        let node1_input = g.input(node1, 0).unwrap();
        assert_eq!(g.link_count(), 0);
        assert!(!g.connected(node0, node1));
        assert!(!g.connected(node1, node0));
        assert_eq!(g.get_connections(node0, node1).count(), 0);
        assert_eq!(g.get_connection(node0, node1), None);

        // Link the same ports thrice
        let (from0, to0) = g.link_ports(node0_output, node1_input).unwrap();
        let (from1, to1) = g.link_ports(node0_output, node1_input).unwrap();
        let (from2, to2) = g.link_ports(node0_output, node1_input).unwrap();
        assert_eq!(from0, SubportIndex::new_multi(node0_output, 0));
        assert_eq!(from1, SubportIndex::new_multi(node0_output, 1));
        assert_eq!(from2, SubportIndex::new_multi(node0_output, 2));
        assert_eq!(to0, SubportIndex::new_multi(node1_input, 0));
        assert_eq!(to1, SubportIndex::new_multi(node1_input, 1));
        assert_eq!(to2, SubportIndex::new_multi(node1_input, 2));
        assert_eq!(g.link_count(), 3);
        assert_eq!(g.subport_link(from0), Some(to0));
        assert_eq!(g.subport_link(to1), Some(from1));
        assert_eq!(
            g.port_links(node0_output).collect_vec(),
            vec![(from0, to0), (from1, to1), (from2, to2)]
        );
        assert_eq!(
            g.get_connections(node0, node1).collect_vec(),
            vec![(from0, to0), (from1, to1), (from2, to2)]
        );
        assert_eq!(g.get_connection(node0, node1), Some((from0, to0)));
        assert!(g.connected(node0, node1));
        assert!(!g.connected(node1, node0));

        let unlinked_to0 = g.unlink_subport(from0).unwrap();
        assert_eq!(unlinked_to0, to0);
        assert_eq!(g.link_count(), 2);
        assert_eq!(
            g.get_connections(node0, node1).collect_vec(),
            vec![(from1, to1), (from2, to2)]
        );
        assert_eq!(g.get_connection(node0, node1), Some((from1, to1)));
        assert!(g.connected(node0, node1));
    }

    #[test]
    fn link_iterators() {
        let mut g = MultiPortGraph::new();
        let node0 = g.add_node(1, 2);
        let node1 = g.add_node(2, 1);
        let (node0_output0, node0_output1) = g.outputs(node0).collect_tuple().unwrap();
        let (node1_input0, node1_input1) = g.inputs(node1).collect_tuple().unwrap();

        assert!(g.input_links(node0).eq([]));
        assert!(g.output_links(node0).eq([]));
        assert!(g.all_links(node0).eq([]));
        assert!(g.input_neighbours(node0).eq([]));
        assert!(g.output_neighbours(node0).eq([]));
        assert!(g.all_neighbours(node0).eq([]));

        g.link_nodes(node0, 0, node1, 0).unwrap();
        g.link_nodes(node0, 0, node1, 1).unwrap();
        g.link_nodes(node0, 1, node1, 1).unwrap();

        assert_eq!(
            g.subport_outputs(node0).collect_vec(),
            [
                SubportIndex::new_multi(node0_output0, 0),
                SubportIndex::new_multi(node0_output0, 1),
                SubportIndex::new_unique(node0_output1),
            ]
        );
        assert_eq!(
            g.subport_inputs(node1).collect_vec(),
            [
                SubportIndex::new_unique(node1_input0),
                SubportIndex::new_multi(node1_input1, 0),
                SubportIndex::new_multi(node1_input1, 1),
            ]
        );

        let links = [
            (
                SubportIndex::new_multi(node0_output0, 0),
                SubportIndex::new_unique(node1_input0),
            ),
            (
                SubportIndex::new_multi(node0_output0, 1),
                SubportIndex::new_multi(node1_input1, 0),
            ),
            (
                SubportIndex::new_unique(node0_output1),
                SubportIndex::new_multi(node1_input1, 1),
            ),
        ];
        assert_eq!(g.input_links(node0).collect_vec(), []);
        assert_eq!(g.output_links(node0).collect_vec(), links);
        assert_eq!(g.all_links(node0).collect_vec(), links);
        assert_eq!(g.input_neighbours(node0).collect_vec(), []);
        assert_eq!(
            g.output_neighbours(node0).collect_vec(),
            [node1, node1, node1]
        );
        assert_eq!(g.all_neighbours(node0).collect_vec(), [node1, node1, node1]);
        assert_eq!(g.port_links(node0_output0).collect_vec(), links[0..2]);
    }
}
