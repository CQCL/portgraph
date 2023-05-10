//! Main definition of the port graph data structure.
//!
//! This module defines the [`PortGraph`] data structure and its associated
//! types. The port graph is a directed graph where each node has a pre-set
//! number of input and output ports, split between [`Direction::Incoming`] and
//! [`Direction::Outgoing`] . Each node has a global [`NodeIndex`] identifier
//! and each port has a global [`PortIndex`] identifier in addition to a local
//! port direction and offset.
//!
//! The number of ports of a node is set at creation time, but can be modified
//! at runtime using [`PortGraph::set_num_ports`].

mod iter;

use std::mem::{replace, take};
use std::num::{NonZeroU16, NonZeroU32};
use std::ops::Range;
use thiserror::Error;

use crate::{Direction, NodeIndex, PortIndex, PortOffset};

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

pub use crate::portgraph::iter::*;

/// An unlabelled port graph.
///
/// A port graph consists of a collection of nodes identified by a [`NodeIndex`].
/// Each node has an ordered sequence of input and output ports, identified by a [`PortIndex`] that is unique within the graph.
/// To optimize for the most common use case, the number of input and output ports of a node must be specified when the node is created.
///
/// When a node and its associated ports are removed their indices will be reused on a best effort basis
/// when a new node is added.
/// The indices of unaffected nodes and ports remain stable.
/// [`PortGraph::compact_nodes`] and [`PortGraph::compact_ports`] to eliminate fragmentation in the index space.
#[cfg_attr(feature = "pyo3", pyclass)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[derive(Clone, PartialEq)]
pub struct PortGraph {
    /// Metadata for each node. Free slots form a linked list.
    node_meta: Vec<NodeEntry>,
    /// Links from ports to other ports. Free ports slabs (fixed-length lists of
    /// ports) form a linked list, with the next slab index stored in the first
    /// port.
    port_link: Vec<Option<PortIndex>>,
    /// Metadata for each port. Ports of a node are stored contiguously, with
    /// incoming ports first.
    port_meta: Vec<PortEntry>,
    /// Index of the first free node slot in the free-node linked list embedded
    /// in `node_meta`.
    node_free: Option<NodeIndex>,
    /// List of free slabs of ports. Each i-th item is the index of the first
    /// slab of size `i+1` in the free-port linked list embedded in `port_link`.
    port_free: Vec<Option<PortIndex>>,
    /// Number of nodes in the graph.
    node_count: usize,
    /// Number of ports in the graph.
    port_count: usize,
    /// Number of links in the graph.
    link_count: usize,
}

impl PortGraph {
    /// Create a new empty [`PortGraph`].
    pub fn new() -> Self {
        Self {
            node_meta: Vec::new(),
            port_link: Vec::new(),
            port_meta: Vec::new(),
            node_free: None,
            port_free: Vec::new(),
            node_count: 0,
            port_count: 0,
            link_count: 0,
        }
    }

    /// Create a new empty [`PortGraph`] with preallocated capacity.
    pub fn with_capacity(nodes: usize, ports: usize) -> Self {
        Self {
            node_meta: Vec::with_capacity(nodes),
            port_link: Vec::with_capacity(ports),
            port_meta: Vec::with_capacity(ports),
            node_free: None,
            port_free: Vec::new(),
            node_count: 0,
            port_count: 0,
            link_count: 0,
        }
    }

    /// Adds a node to the portgraph with a given number of input and output ports.
    ///
    /// # Panics
    ///
    /// Panics if the total number of ports exceeds `u16::MAX`.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::PortGraph;
    /// # use portgraph::Direction;
    /// let mut g = PortGraph::new();
    /// let node = g.add_node(4, 3);
    /// assert_eq!(g.inputs(node).count(), 4);
    /// assert_eq!(g.outputs(node).count(), 3);
    /// assert!(g.contains_node(node));
    /// ```
    pub fn add_node(&mut self, incoming: usize, outgoing: usize) -> NodeIndex {
        assert!(
            incoming <= NodeMeta::MAX_INCOMING,
            "Incoming port count exceeds maximum."
        );
        assert!(
            outgoing <= NodeMeta::MAX_OUTGOING,
            "Outgoing port count exceeds maximum."
        );
        assert!(
            incoming + outgoing <= u16::MAX as usize,
            "Total port count exceeds maximum u16::MAX."
        );

        let node = self.alloc_node();
        let node_meta = self.alloc_ports(node, incoming, outgoing, 0);
        self.node_meta[node.index()] = NodeEntry::Node(node_meta);

        self.node_count += 1;
        self.port_count += incoming + outgoing;

        node
    }

    #[inline]
    fn alloc_node(&mut self) -> NodeIndex {
        match self.node_free {
            Some(node) => {
                let NodeEntry::Free(next) = self.node_meta[node.index()] else {
                    unreachable!("non free node on free list");
                };

                self.node_free = next;
                node
            }
            None => {
                let index = self.node_meta.len();
                self.node_meta.push(NodeEntry::Free(None));
                NodeIndex::new(index)
            }
        }
    }

    /// Allocates a slab of ports. Returns the index of the first port, and the
    /// number of ports in the slab.
    #[inline]
    fn alloc_ports(
        &mut self,
        node: NodeIndex,
        incoming: usize,
        outgoing: usize,
        extra_capacity: usize,
    ) -> NodeMeta {
        let requested = incoming + outgoing + extra_capacity;
        let meta_incoming = PortEntry::Port(PortMeta::new(node, Direction::Incoming));
        let meta_outgoing = PortEntry::Port(PortMeta::new(node, Direction::Outgoing));
        let meta_empty = PortEntry::Free;

        if requested == 0 {
            return NodeMeta::default();
        }

        match self.port_free.get(requested - 1).copied().flatten() {
            Some(port) => {
                // TODO: Over-allocate if there are similarly-sized free slabs.
                let capacity = requested;

                let free_next = take(&mut self.port_link[port.index()]);
                self.port_free[requested - 1] = free_next;

                let node_meta =
                    NodeMeta::new(port, incoming as u16, outgoing as u16, capacity as u16);
                self.port_meta[node_meta.incoming_ports()].fill(meta_incoming);
                self.port_meta[node_meta.outgoing_ports()].fill(meta_outgoing);
                self.port_meta[node_meta.unused_ports()].fill(meta_empty);
                self.port_link[port.index()..port.index() + capacity].fill(None);

                node_meta
            }
            None => {
                debug_assert_eq!(self.port_meta.len(), self.port_link.len());
                let old_len = self.port_meta.len();
                let port = PortIndex::new(old_len);
                let capacity = requested;

                self.port_meta.reserve(requested);
                self.port_meta.resize(old_len + incoming, meta_incoming);
                self.port_meta
                    .resize(old_len + incoming + outgoing, meta_outgoing);
                self.port_meta.resize(old_len + capacity, meta_empty);
                self.port_link.resize(old_len + capacity, None);

                NodeMeta::new(port, incoming as u16, outgoing as u16, capacity as u16)
            }
        }
    }

    /// Remove a node from the port graph. All ports of the node will be
    /// unlinked and removed as well. Does nothing if the node does not exist.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::PortGraph;
    /// # use portgraph::Direction;
    /// let mut g = PortGraph::new();
    /// let node0 = g.add_node(1, 1);
    /// let node1 = g.add_node(1, 1);
    /// g.link_ports(g.outputs(node0).nth(0).unwrap(), g.inputs(node1).nth(0).unwrap());
    /// g.link_ports(g.outputs(node1).nth(0).unwrap(), g.inputs(node0).nth(0).unwrap());
    /// g.remove_node(node0);
    /// assert!(!g.contains_node(node0));
    /// assert!(g.port_link(g.outputs(node1).nth(0).unwrap()).is_none());
    /// assert!(g.port_link(g.inputs(node1).nth(0).unwrap()).is_none());
    /// ```
    pub fn remove_node(&mut self, node: NodeIndex) {
        let Some(node_meta) = self.node_meta.get(node.index()).copied() else {
            return;
        };

        let NodeEntry::Node(node_meta) = node_meta else {
            return;
        };

        self.free_node(node);

        self.node_count -= 1;

        if node_meta.capacity() > 0 {
            let port_list = node_meta.port_list();
            let size = node_meta.capacity();
            self.port_count -= node_meta.port_count();

            assert!(port_list.index() + size <= self.port_link.len());
            assert!(port_list.index() + size <= self.port_meta.len());

            self.free_ports(port_list, size);
        }
    }

    #[inline]
    fn free_node(&mut self, node: NodeIndex) {
        self.node_meta[node.index()] = NodeEntry::Free(self.node_free);
        self.node_free = Some(node);
    }

    /// Free a slab of ports.
    ///
    /// Disconnects all links and adds the slab to the free port list.
    #[inline]
    fn free_ports(&mut self, ports: PortIndex, size: usize) {
        if size > self.port_free.len() {
            self.port_free.resize(size, None);
        }

        let ports_free = &mut self.port_free[size - 1];

        for i in ports.index()..ports.index() + size {
            self.port_meta[i] = PortEntry::Free;

            if let Some(link) = self.port_link[i].take() {
                self.port_link[link.index()] = None;
                self.link_count -= 1;
            }
        }

        // Add this slab to the free list.
        self.port_link[ports.index()] = replace(ports_free, Some(ports));
    }

    /// Link an output port to an input port.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::PortGraph;
    /// # use portgraph::Direction;
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
    ///  - When `port_from` or `port_to` does not exist.
    ///  - When `port_from` is not an output port.
    ///  - When `port_to` is not an input port.
    ///  - When `port_from` or `port_to` is already linked.
    pub fn link_ports(
        &mut self,
        port_from: PortIndex,
        port_to: PortIndex,
    ) -> Result<(), LinkError> {
        let Some(meta_from) = self.port_meta_valid(port_from) else {
            return Err(LinkError::UnknownPort{port: port_from});
        };

        let Some(meta_to) = self.port_meta_valid(port_to) else {
            return Err(LinkError::UnknownPort{port: port_from});
        };

        if meta_from.direction() != Direction::Outgoing {
            return Err(LinkError::UnexpectedDirection {
                port: port_from,
                dir: meta_from.direction(),
            });
        } else if meta_to.direction() != Direction::Incoming {
            return Err(LinkError::UnexpectedDirection {
                port: port_to,
                dir: meta_to.direction(),
            });
        }

        if self.port_link[port_from.index()].is_some() {
            return Err(LinkError::AlreadyLinked { port: port_from });
        } else if self.port_link[port_to.index()].is_some() {
            return Err(LinkError::AlreadyLinked { port: port_to });
        }

        self.port_link[port_from.index()] = Some(port_to);
        self.port_link[port_to.index()] = Some(port_from);
        self.link_count += 1;
        Ok(())
    }

    /// Unlinks the `port` and returns the port it was linked to. Returns `None`
    /// when the port was not linked.
    pub fn unlink_port(&mut self, port: PortIndex) -> Option<PortIndex> {
        self.port_meta_valid(port)?;
        let linked = take(&mut self.port_link[port.index()])?;
        self.port_link[linked.index()] = None;
        self.link_count -= 1;
        Some(linked)
    }

    /// Returns an iterator over every pair of matching ports connecting `from`
    /// with `to`.
    ///
    /// # Example
    /// ```
    /// # use portgraph::{PortGraph, NodeIndex, PortIndex, Direction};
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
    #[inline]
    pub fn get_connections(&self, from: NodeIndex, to: NodeIndex) -> NodeConnections<'_> {
        NodeConnections::new(self, to, self.outputs(from), self.output_links(from))
    }

    /// Checks whether there is a directed link between the two nodes and
    /// returns the first matching pair of ports.
    ///
    /// # Example
    /// ```
    /// # use portgraph::{PortGraph, NodeIndex, PortIndex, Direction};
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
    #[inline]
    pub fn get_connection(&self, from: NodeIndex, to: NodeIndex) -> Option<(PortIndex, PortIndex)> {
        self.get_connections(from, to).next()
    }

    /// Checks whether there is a directed link between the two nodes.
    ///
    /// # Example
    /// ```
    /// # use portgraph::{PortGraph, NodeIndex, PortIndex, Direction};
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
    pub fn connected(&self, from: NodeIndex, to: NodeIndex) -> bool {
        self.get_connection(from, to).is_some()
    }

    /// Links two nodes at an input and output port offsets.
    pub fn link_nodes(
        &mut self,
        from: NodeIndex,
        from_offset: usize,
        to: NodeIndex,
        to_offset: usize,
    ) -> Result<(PortIndex, PortIndex), LinkError> {
        let from_port = self
            .output(from, from_offset)
            .ok_or(LinkError::UnknownOffset {
                node: from,
                offset: PortOffset::new_outgoing(from_offset),
            })?;
        let to_port = self.input(to, to_offset).ok_or(LinkError::UnknownOffset {
            node: to,
            offset: PortOffset::new_incoming(to_offset),
        })?;
        self.link_ports(from_port, to_port)?;
        Ok((from_port, to_port))
    }

    /// Returns the direction of the `port`.
    #[inline]
    pub fn port_direction(&self, port: PortIndex) -> Option<Direction> {
        Some(self.port_meta_valid(port)?.direction())
    }

    /// Returns the node that the `port` belongs to.
    #[inline]
    pub fn port_node(&self, port: PortIndex) -> Option<NodeIndex> {
        Some(self.port_meta_valid(port)?.node())
    }

    /// Returns the index of a `port` within its node's port list.
    pub fn port_offset(&self, port: PortIndex) -> Option<PortOffset> {
        let port_meta = self.port_meta_valid(port)?;
        let node = port_meta.node();

        let node_meta = match self.node_meta[node.index()] {
            NodeEntry::Free(_) => unreachable!("ports are only attached to valid nodes"),
            NodeEntry::Node(node_meta) => node_meta,
        };

        let port_offset = port.index().wrapping_sub(node_meta.port_list().index());

        match port_meta.direction() {
            Direction::Incoming => Some(PortOffset::new_incoming(port_offset)),
            Direction::Outgoing => {
                let port_offset = port_offset.saturating_sub(node_meta.incoming() as usize);
                Some(PortOffset::new_outgoing(port_offset))
            }
        }
    }

    /// Returns the port index for a given node, direction, and offset.
    #[must_use]
    pub fn port_index(&self, node: NodeIndex, offset: PortOffset) -> Option<PortIndex> {
        let node_meta = self.node_meta_valid(node)?;
        let direction = offset.direction();
        let offset = offset.index();
        node_meta.ports(direction).nth(offset).map(PortIndex::new)
    }

    /// Returns the port that the given `port` is linked to.
    #[inline]
    pub fn port_link(&self, port: PortIndex) -> Option<PortIndex> {
        self.port_meta_valid(port)?;
        self.port_link[port.index()]
    }

    /// Iterates over all the ports of the `node` in the given `direction`.
    pub fn ports(&self, node: NodeIndex, direction: Direction) -> NodePorts {
        match self.node_meta_valid(node) {
            Some(node_meta) => NodePorts {
                indices: node_meta.ports(direction),
            },
            None => NodePorts::default(),
        }
    }

    /// Iterates over the input and output ports of the `node` in sequence.
    pub fn all_ports(&self, node: NodeIndex) -> NodePorts {
        match self.node_meta_valid(node) {
            Some(node_meta) => NodePorts {
                indices: node_meta.all_ports(),
            },
            None => NodePorts::default(),
        }
    }

    /// Returns the input port at the given offset in the `node`.
    ///
    /// Shorthand for [`PortGraph::port_index`].
    #[inline]
    pub fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.port_index(node, PortOffset::new_incoming(offset))
    }

    /// Returns the output port at the given offset in the `node`.
    ///
    /// Shorthand for [`PortGraph::ports`].
    #[inline]
    pub fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.port_index(node, PortOffset::new_outgoing(offset))
    }

    /// Iterates over all the input ports of the `node`.
    ///
    /// Shorthand for [`PortGraph::ports`].
    #[inline]
    pub fn inputs(&self, node: NodeIndex) -> NodePorts {
        self.ports(node, Direction::Incoming)
    }

    /// Iterates over all the output ports of the `node`.
    ///
    /// Shorthand for [`PortGraph::ports`].
    #[inline]
    pub fn outputs(&self, node: NodeIndex) -> NodePorts {
        self.ports(node, Direction::Outgoing)
    }

    /// Returns the number of input ports of the `node`.
    ///
    /// Shorthand for [`PortGraph::num_ports`].
    #[inline]
    pub fn num_inputs(&self, node: NodeIndex) -> usize {
        self.num_ports(node, Direction::Incoming)
    }

    /// Returns the number of output ports of the `node`.
    ///
    /// Shorthand for [`PortGraph::num_ports`].
    #[inline]
    pub fn num_outputs(&self, node: NodeIndex) -> usize {
        self.num_ports(node, Direction::Outgoing)
    }

    /// Returns the number of ports of the `node` in the given `direction`.
    #[inline]
    pub fn num_ports(&self, node: NodeIndex, direction: Direction) -> usize {
        let Some(node_meta) = self.node_meta_valid(node) else {return 0;};
        if Direction::Incoming == direction {
            node_meta.incoming() as usize
        } else {
            node_meta.outgoing() as usize
        }
    }

    /// Iterates over all the port offsets of the `node` in the given `direction`.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::PortGraph;
    /// # use portgraph::{Direction, PortOffset};
    /// let mut graph = PortGraph::new();
    /// let node = graph.add_node(0, 2);
    ///
    /// assert!(graph.links(node, Direction::Incoming).eq([]));
    /// assert!(graph.port_offsets(node, Direction::Outgoing).eq([PortOffset::new_outgoing(0), PortOffset::new_outgoing(1)]));
    /// ```
    pub fn port_offsets(&self, node: NodeIndex, direction: Direction) -> NodePortOffsets {
        match direction {
            Direction::Incoming => NodePortOffsets {
                incoming: 0..self.num_inputs(node) as u16,
                outgoing: 0..0,
            },
            Direction::Outgoing => NodePortOffsets {
                incoming: 0..0,
                outgoing: 0..self.num_outputs(node) as u32,
            },
        }
    }

    /// Iterates over all the input port offsets of the `node`.
    ///
    /// Shorthand for [`PortGraph::port_offsets`].
    #[inline]
    pub fn input_offsets(&self, node: NodeIndex) -> NodePortOffsets {
        self.port_offsets(node, Direction::Incoming)
    }

    /// Iterates over all the output port offsets of the `node`.
    ///
    /// Shorthand for [`PortGraph::port_offsets`].
    #[inline]
    pub fn output_offsets(&self, node: NodeIndex) -> NodePortOffsets {
        self.port_offsets(node, Direction::Outgoing)
    }

    /// Iterates over the input and output port offsets of the `node` in sequence.
    #[inline]
    pub fn all_port_offsets(&self, node: NodeIndex) -> NodePortOffsets {
        NodePortOffsets {
            incoming: 0..self.num_inputs(node) as u16,
            outgoing: 0..self.num_outputs(node) as u32,
        }
    }

    /// Iterates over the links of the `node` in the given `direction`. When the
    /// corresponding node port is linked to another one, the Option contains
    /// the index of the other port.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::PortGraph;
    /// # use portgraph::Direction;
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
    /// assert!(graph.links(node_a, Direction::Outgoing).eq([Some(port_b), None]));
    /// assert!(graph.links(node_b, Direction::Incoming).eq([Some(port_a)]));
    /// ```
    #[inline]
    pub fn links(&self, node: NodeIndex, direction: Direction) -> NodeLinks<'_> {
        let Some(node_meta) = self.node_meta_valid(node) else {
            return NodeLinks([].iter());
        };
        let indices = node_meta.ports(direction);
        NodeLinks(self.port_link[indices].iter())
    }

    /// Iterates over the input links of the `node`. Shorthand for [`PortGraph::links`].
    #[inline]
    pub fn input_links(&self, node: NodeIndex) -> NodeLinks<'_> {
        self.links(node, Direction::Incoming)
    }

    /// Iterates over the output links of the `node`. Shorthand for [`PortGraph::links`].
    #[inline]
    pub fn output_links(&self, node: NodeIndex) -> NodeLinks<'_> {
        self.links(node, Direction::Outgoing)
    }

    /// Iterates over the input and output links of the `node` in sequence.
    #[inline]
    pub fn all_links(&self, node: NodeIndex) -> NodeLinks<'_> {
        let Some(node_meta) = self.node_meta_valid(node) else {
            return NodeLinks([].iter());
        };
        let indices = node_meta.all_ports();
        NodeLinks(self.port_link[indices].iter())
    }

    /// Iterates over neighbour nodes in the given `direction`.
    /// May contain duplicates if the graph has multiple links between nodes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::PortGraph;
    /// # use portgraph::Direction;
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
    #[inline]
    pub fn neighbours(&self, node: NodeIndex, direction: Direction) -> Neighbours<'_> {
        Neighbours::from_node_links(self, self.links(node, direction))
    }

    /// Iterates over the input neighbours of the `node`. Shorthand for [`PortGraph::links`].
    #[inline]
    pub fn input_neighbours(&self, node: NodeIndex) -> Neighbours<'_> {
        self.neighbours(node, Direction::Incoming)
    }

    /// Iterates over the output neighbours of the `node`. Shorthand for [`PortGraph::links`].
    #[inline]
    pub fn output_neighbours(&self, node: NodeIndex) -> Neighbours<'_> {
        self.neighbours(node, Direction::Outgoing)
    }

    /// Iterates over the input and output neighbours of the `node` in sequence.
    #[inline]
    pub fn all_neighbours(&self, node: NodeIndex) -> Neighbours<'_> {
        Neighbours::from_node_links(self, self.all_links(node))
    }

    /// Returns whether the port graph contains the `node`.
    #[inline]
    pub fn contains_node(&self, node: NodeIndex) -> bool {
        self.node_meta_valid(node).is_some()
    }

    /// Returns whether the port graph contains the `port`.
    #[inline]
    pub fn contains_port(&self, port: PortIndex) -> bool {
        self.port_meta_valid(port).is_some()
    }

    /// Returns whether the port graph has no nodes nor ports.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.node_count == 0 && self.port_count == 0
    }

    /// Returns the number of nodes in the port graph.
    #[inline]
    pub fn node_count(&self) -> usize {
        self.node_count
    }

    /// Returns the number of ports in the port graph.
    #[inline]
    pub fn port_count(&self) -> usize {
        self.port_count
    }

    /// Returns the number of links between ports.
    #[inline]
    pub fn link_count(&self) -> usize {
        self.link_count
    }

    /// Iterates over the nodes in the port graph.
    #[inline]
    pub fn nodes_iter(&self) -> Nodes<'_> {
        Nodes {
            iter: self.node_meta.iter().enumerate(),
            len: self.node_count,
        }
    }

    /// Iterates over the ports in the port graph.
    #[inline]
    pub fn ports_iter(&self) -> Ports<'_> {
        Ports {
            iter: self.port_meta.iter().enumerate(),
            len: self.port_count,
        }
    }

    /// Removes all nodes and ports from the port graph.
    pub fn clear(&mut self) {
        self.node_meta.clear();
        self.port_link.clear();
        self.port_meta.clear();
        self.node_free = None;
        self.port_free.clear();
        self.node_count = 0;
        self.port_count = 0;
        self.link_count = 0;
    }

    /// Returns the capacity of the underlying buffer for nodes.
    #[inline]
    pub fn node_capacity(&self) -> usize {
        self.node_meta.capacity()
    }

    /// Returns the capacity of the underlying buffer for ports.
    #[inline]
    pub fn port_capacity(&self) -> usize {
        self.port_meta.capacity()
    }

    /// Returns the allocated port capacity for a specific node.
    ///
    /// Changes to the number of ports of the node will not reallocate
    /// until the number of ports exceeds this capacity.
    #[inline]
    pub fn node_port_capacity(&self, node: NodeIndex) -> usize {
        self.node_meta_valid(node)
            .map_or(0, |node_meta| node_meta.capacity())
    }

    /// Reserves enough capacity to insert at least the given number of additional nodes and ports.
    ///
    /// This method does not take into account the length of the free list and might overallocate speculatively.
    pub fn reserve(&mut self, nodes: usize, ports: usize) {
        self.node_meta.reserve(nodes);
        self.port_meta.reserve(ports);
        self.port_link.reserve(ports);
    }

    /// Changes the number of ports of the `node` to the given `incoming` and `outgoing` counts.
    ///
    /// Invalidates the indices of the node's ports. If the number of incoming or outgoing ports
    /// is reduced, the ports are removed from the end of the port list.
    ///
    /// Every time a port is moved, the `rekey` function will be called with its old and new index.
    /// If the port is removed, the new index will be `None`.
    ///
    /// This operation is O(n) where n is the number of ports of the node.
    pub fn set_num_ports<F>(
        &mut self,
        node: NodeIndex,
        incoming: usize,
        outgoing: usize,
        mut rekey: F,
    ) where
        F: FnMut(PortIndex, Option<PortIndex>),
    {
        assert!(
            incoming <= NodeMeta::MAX_INCOMING,
            "Incoming port count exceeds maximum."
        );
        assert!(
            outgoing <= NodeMeta::MAX_OUTGOING,
            "Outgoing port count exceeds maximum."
        );

        let new_total = incoming + outgoing;

        let Some(node_meta) = self.node_meta_valid(node) else {return;};
        let old_incoming = node_meta.incoming() as usize;
        let old_outgoing = node_meta.outgoing() as usize;
        let old_capacity = node_meta.capacity();
        let old_total = old_incoming + old_outgoing;
        let old_port_list = node_meta.port_list();
        if old_incoming == incoming && old_outgoing == outgoing {
            // Nothing to do
            return;
        }
        // Disconnect any port to be removed.
        for port in self
            .inputs(node)
            .skip(incoming)
            .chain(self.outputs(node).skip(outgoing))
        {
            self.unlink_port(port);
            rekey(port, None);
        }

        if 0 < new_total && new_total <= old_capacity {
            // Special case when we can avoid reallocations by shifting the
            // ports in the pre-allocated slab.
            self.resize_ports_inplace(node, incoming, outgoing, rekey);
            return;
        }
        // Allocate a new slab of ports. If `new_total` is 0, we just free the
        // old slab.
        //
        // TODO: Fine-tune overallocation factor
        let target_capacity = new_total.next_power_of_two();
        let new_meta = self.alloc_ports(node, incoming, outgoing, target_capacity - new_total);

        // Move the port data.
        for dir in Direction::BOTH {
            let rekeys = node_meta.ports(dir).zip(new_meta.ports(dir));
            for (old, new) in rekeys {
                if let Some(link) = self.port_link[old] {
                    self.port_link[link.index()] = Some(PortIndex::new(new));
                }
                self.port_link[new] = self.port_link[old].take();
                self.port_meta[new] = self.port_meta[old];

                rekey(PortIndex::new(old), Some(PortIndex::new(new)));
            }
        }

        self.node_meta[node.index()] = NodeEntry::Node(new_meta);
        self.free_ports(old_port_list, old_capacity);

        self.port_count = self.port_count - old_total + new_total;
    }

    /// Compacts the storage of nodes in the portgraph so that all nodes are stored consecutively.
    ///
    /// Every time a node is moved, the `rekey` function will be called with its old and new index.
    pub fn compact_nodes<F>(&mut self, mut rekey: F)
    where
        F: FnMut(NodeIndex, NodeIndex),
    {
        let mut old_index = 0;
        let mut new_index = 0;
        self.node_meta.retain(|node_meta| {
            let old_node = NodeIndex::new(old_index);
            let new_node = NodeIndex::new(new_index);

            let NodeEntry::Node(node_meta) = node_meta else {
                old_index += 1;
                return false;
            };

            for dir in Direction::BOTH {
                for port in node_meta.ports(dir) {
                    self.port_meta[port] = PortEntry::Port(PortMeta::new(new_node, dir));
                }
            }

            rekey(old_node, new_node);

            old_index += 1;
            new_index += 1;
            true
        });

        self.node_free = None;
    }

    /// Compacts the storage of ports in the portgraph so that all ports are stored consecutively.
    ///
    /// Shrinks the port capacity of every node to match the number of ports it contains.
    ///
    /// Every time a port is moved, the `rekey` function will be called with is old and new index.
    pub fn compact_ports<F>(&mut self, mut rekey: F)
    where
        F: FnMut(PortIndex, PortIndex),
    {
        // Compact the links vector, ignoring free ports.
        let mut new_index = 0;
        for old_index in 0..self.port_link.len() {
            if let PortEntry::Free = self.port_meta[old_index] {
                continue;
            }
            if new_index == old_index {
                new_index += 1;
                continue;
            }

            // Invariant: The neighbour ports of visited ports always have
            // backlinks pointing to the correctly updated port indices.
            //
            // At the end of the loop, all port links have been updated.
            if let Some(link) = self.port_link[old_index] {
                self.port_link[link.index()] = Some(PortIndex::new(new_index));
            }
            self.port_link.swap(new_index, old_index);
            new_index += 1;
        }
        self.port_link.truncate(new_index);

        // Compact the metadata vector
        let mut new_index = 0;
        let mut old_index = 0;
        self.port_meta.retain(|port_meta| {
            let old_port = PortIndex::new(old_index);
            let new_port = PortIndex::new(new_index);

            let PortEntry::Port(port_meta) = port_meta else {
                old_index += 1;
                return false;
            };

            // If we are moving the first port in a node's port list, we have to update the node.
            let node_entry = &mut self.node_meta[port_meta.node().index()];
            let NodeEntry::Node(node_meta) = *node_entry else {
                unreachable!("port must be attached to a valid node")
            };
            if node_meta.port_list() == old_port {
                // Update the node's port list, and reduce the capacity to match
                // the number of ports.
                *node_entry = NodeEntry::Node(NodeMeta::new(
                    new_port,
                    node_meta.incoming(),
                    node_meta.outgoing(),
                    node_meta.port_count() as u16,
                ));
            }

            rekey(old_port, new_port);

            old_index += 1;
            new_index += 1;
            true
        });

        self.port_free.clear();
    }

    /// Shrinks the underlying buffers to the fit the data.
    ///
    /// This does not move nodes or ports, which might prevent freeing up more capacity.
    /// To shrink the buffers as much as possible, call [`PortGraph::compact_nodes`] and
    /// [`PortGraph::compact_ports`] first.
    pub fn shrink_to_fit(&mut self) {
        self.node_meta.shrink_to_fit();
        self.port_link.shrink_to_fit();
        self.port_meta.shrink_to_fit();
        self.port_free.shrink_to_fit();
    }

    #[inline]
    fn node_meta_valid(&self, node: NodeIndex) -> Option<NodeMeta> {
        match self.node_meta.get(node.index()) {
            Some(NodeEntry::Node(node_meta)) => Some(*node_meta),
            _ => None,
        }
    }

    #[inline]
    #[must_use]
    fn port_meta_valid(&self, port: PortIndex) -> Option<PortMeta> {
        match self.port_meta.get(port.index()) {
            Some(PortEntry::Port(port_meta)) => Some(*port_meta),
            _ => None,
        }
    }

    /// Change the number of incoming and outgoing ports of a node, without
    /// altering the total.
    ///
    /// This operation avoids changing the number of incoming and outgoing ports
    /// without reallocating, but requires maintaining the total number of
    /// ports.
    ///
    /// Every time a port is moved, the `rekey` function will be called with its old and new index.
    /// If the port is removed, the new index will be `None`.
    ///
    /// # Panics
    ///
    /// If `incoming + outgoing` is more than the allocated port capacity.
    fn resize_ports_inplace<F>(
        &mut self,
        node: NodeIndex,
        incoming: usize,
        outgoing: usize,
        mut rekey: F,
    ) where
        F: FnMut(PortIndex, Option<PortIndex>),
    {
        let node_meta = self.node_meta_valid(node).expect("Node must be valid");
        let new_meta = NodeMeta::new(
            node_meta.port_list(),
            incoming as u16,
            outgoing as u16,
            node_meta.capacity() as u16,
        );

        // Disconnect any port to be removed.
        for port in self
            .inputs(node)
            .skip(incoming)
            .chain(self.outputs(node).skip(outgoing))
        {
            self.unlink_port(port);
            rekey(port, None);
        }

        let move_port = |(old, new)| {
            let old_port = PortIndex::new(old);
            let new_port = PortIndex::new(new);
            self.port_link[new] = self.port_link[old];
            self.port_meta[new] = self.port_meta[old];
            rekey(old_port, Some(new_port));
            if let Some(link) = self.port_link[new] {
                self.port_link[link.index()] = Some(new_port);
            }
        };

        // Choose whether to move the ports starting from the first or from the
        // last depending on the shift direction, to avoid overwriting valid
        // data.
        let pairs = node_meta.outgoing_ports().zip(new_meta.outgoing_ports());
        if (node_meta.incoming() as usize) > incoming {
            pairs.for_each(move_port);
        } else {
            pairs.rev().for_each(move_port);
        };

        // Initialize the new ports
        for dir in Direction::BOTH {
            let existing = node_meta.num_ports(dir) as usize;
            for port in new_meta.ports(dir).skip(existing) {
                self.port_link[port] = None;
                self.port_meta[port] = PortEntry::Port(PortMeta::new(node, dir));
            }
        }
        // Empty ports that are no longer used.
        for port in new_meta.port_count()..node_meta.port_count() {
            self.port_link[port] = None;
            self.port_meta[port] = PortEntry::Free;
        }

        self.node_meta[node.index()] = NodeEntry::Node(new_meta);
    }
}

impl Default for PortGraph {
    fn default() -> Self {
        Self::new()
    }
}

/// Meta data stored for a valid node.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
struct NodeMeta {
    /// The index of the first port in the port list.
    /// If the node has no ports, this will point to the index 0.
    port_list: PortIndex,
    /// The number of incoming ports plus 1.
    /// We use the `NonZeroU16` here to ensure that `NodeEntry` is 8 bytes.
    incoming: NonZeroU16,
    /// The number of outgoing ports.
    outgoing: u16,
    /// The port capacity allocated to this node. Changing the number of ports
    /// up to this capacity does not require reallocation.
    capacity: u16,
}

impl NodeMeta {
    /// The maximum number of incoming ports for a node.
    /// This is restricted by the `NonZeroU16` representation.
    const MAX_INCOMING: usize = u16::MAX as usize - 1;
    /// The maximum number of outgoing ports for a node.
    const MAX_OUTGOING: usize = u16::MAX as usize;

    #[inline]
    pub fn new(port_list: PortIndex, incoming: u16, outgoing: u16, capacity: u16) -> Self {
        assert!(incoming <= Self::MAX_INCOMING as u16);
        assert!(outgoing <= Self::MAX_OUTGOING as u16);
        assert!(incoming.saturating_add(outgoing) <= capacity);
        assert!(capacity > 0 || port_list.index() == 0);
        Self {
            port_list,
            // SAFETY: The value cannot be zero, and won't overflow.
            incoming: unsafe { NonZeroU16::new_unchecked(incoming + 1) },
            outgoing,
            capacity,
        }
    }

    #[inline]
    pub fn port_list(&self) -> PortIndex {
        self.port_list
    }

    /// Returns the number of incoming ports.
    #[inline]
    pub fn incoming(&self) -> u16 {
        u16::from(self.incoming).wrapping_sub(1)
    }

    /// Returns the number of outgoing ports.
    #[inline]
    pub fn outgoing(&self) -> u16 {
        self.outgoing
    }

    /// Returns the number of ports in a given direction.
    pub fn num_ports(&self, dir: Direction) -> u16 {
        match dir {
            Direction::Incoming => self.incoming(),
            Direction::Outgoing => self.outgoing(),
        }
    }

    /// Returns the total number ports.
    #[inline]
    pub fn port_count(&self) -> usize {
        self.outgoing as usize + self.incoming() as usize
    }

    /// Returns the allocated port capacity for this node.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity as usize
    }

    /// Returns a range over the port indices of this node.
    #[inline]
    pub fn all_ports(&self) -> Range<usize> {
        let start = self.port_list.index();
        let end = start + self.incoming() as usize + self.outgoing() as usize;
        start..end
    }

    /// Returns a range over the port indices of this node in a given direction.
    #[inline]
    pub fn ports(&self, direction: Direction) -> Range<usize> {
        match direction {
            Direction::Incoming => self.incoming_ports(),
            Direction::Outgoing => self.outgoing_ports(),
        }
    }

    /// Returns a range over the incoming port indices of this node.
    #[inline]
    pub fn incoming_ports(&self) -> Range<usize> {
        let start = self.port_list.index();
        let end = start + self.incoming() as usize;
        start..end
    }

    /// Returns a range over the outgoing port indices of this node.
    #[inline]
    pub fn outgoing_ports(&self) -> Range<usize> {
        let start = self.port_list.index() + self.incoming() as usize;
        let end = start + self.outgoing() as usize;
        start..end
    }

    /// Returns a range over the unused pre-allocated port indices of this node.
    #[inline]
    pub fn unused_ports(&self) -> Range<usize> {
        let start = self.port_list.index() + self.port_count();
        let end = self.port_list.index() + self.capacity();
        start..end
    }
}

impl Default for NodeMeta {
    fn default() -> Self {
        Self::new(PortIndex::default(), 0, 0, 0)
    }
}

/// Meta data stored for a node, which might be free.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
enum NodeEntry {
    /// No node is stored at this entry.
    /// Instead the entry contains the next index in the node free list.
    #[cfg_attr(feature = "serde", serde(rename = "f",))]
    Free(Option<NodeIndex>),
    /// A node is stored at this entry.
    ///
    /// This value allows for null-value optimization so that
    /// `size_of::<NodeEntry>() == size_of::<NodeMeta>()`.
    #[cfg_attr(feature = "serde", serde(rename = "n"))]
    Node(NodeMeta),
}

impl std::fmt::Debug for PortGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PortGraph")
            .field("nodes", &debug::NodesDebug(self))
            .field("ports", &debug::PortsDebug(self))
            .finish()
    }
}

mod debug {
    use super::*;
    pub struct NodesDebug<'a>(pub &'a PortGraph);

    impl<'a> std::fmt::Debug for NodesDebug<'a> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_map()
                .entries(
                    self.0
                        .nodes_iter()
                        .map(|node| (node, NodeDebug(self.0, node))),
                )
                .finish()
        }
    }

    pub struct NodeDebug<'a>(pub &'a PortGraph, pub NodeIndex);

    impl<'a> std::fmt::Debug for NodeDebug<'a> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let inputs: Vec<_> = self.0.inputs(self.1).collect();
            let outputs: Vec<_> = self.0.outputs(self.1).collect();

            f.debug_struct("Node")
                .field("inputs", &inputs)
                .field("outputs", &outputs)
                .finish()
        }
    }

    pub struct PortsDebug<'a>(pub &'a PortGraph);

    impl<'a> std::fmt::Debug for PortsDebug<'a> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_map()
                .entries(
                    self.0
                        .ports_iter()
                        .map(|port| (port, PortDebug(self.0, port))),
                )
                .finish()
        }
    }

    pub struct PortDebug<'a>(pub &'a PortGraph, pub PortIndex);

    impl<'a> std::fmt::Debug for PortDebug<'a> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let direction = self.0.port_direction(self.1).unwrap();
            let link = self.0.port_link(self.1);
            let node = self.0.port_node(self.1).unwrap();

            let mut fmt_struct = f.debug_struct("Port");
            fmt_struct.field("node", &node);
            fmt_struct.field("direction", &direction);

            if let Some(link) = link {
                fmt_struct.field("link", &link);
            }

            fmt_struct.finish()
        }
    }
}

/// Meta data stored for a valid port.
///
/// Encodes a `NodeIndex` and a `Direction` by using the last bit.
/// We use a `NonZeroU32` here to ensure that `PortEntry` only uses 4 bytes.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
struct PortMeta(NonZeroU32);

impl PortMeta {
    const DIRECTION_BIT: u32 = u32::BITS - 1;
    const NODE_MASK: u32 = !(1 << Self::DIRECTION_BIT);

    #[inline]
    pub fn new(node: NodeIndex, direction: Direction) -> Self {
        let direction = (direction as u32) << Self::DIRECTION_BIT;
        let index = node.index() as u32 + 1;
        // SAFETY: We know that this can not be zero
        Self(unsafe { NonZeroU32::new_unchecked(index | direction) })
    }

    #[inline]
    pub fn node(self) -> NodeIndex {
        // PERFORMANCE: Make sure that this does not involve a check
        NodeIndex::new((u32::from(self.0) & Self::NODE_MASK) as usize - 1)
    }

    #[inline]
    pub fn direction(self) -> Direction {
        if u32::from(self.0) >> Self::DIRECTION_BIT == 0 {
            Direction::Incoming
        } else {
            Direction::Outgoing
        }
    }
}

/// Meta data stored for a port, which might be free.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize), serde(untagged))]
enum PortEntry {
    /// No port is stored at this entry.
    /// The index will be part of a port list currently on the free list.
    Free,
    /// A port is stored at this entry.
    Port(PortMeta),
}

/// Error generated when linking ports.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum LinkError {
    /// The port is already linked.
    #[error("port {port:?} is already linked")]
    AlreadyLinked { port: PortIndex },
    /// The port does not exist.
    #[error("unknown port '{port:?}''")]
    UnknownPort { port: PortIndex },
    /// The port offset is invalid.
    #[error("unknown port offset {} in node {node:?} in direction {:?}", offset.index(), offset.direction())]
    UnknownOffset { node: NodeIndex, offset: PortOffset },
    /// The port cannot be linked in this direction.
    #[error("port {port:?} had an unexpected direction {dir:?} during a link operation")]
    UnexpectedDirection { port: PortIndex, dir: Direction },
}

#[cfg(test)]
pub mod test {
    #[cfg(feature = "serde")]
    #[cfg(feature = "proptest")]
    use crate::proptest::gen_portgraph;
    #[cfg(feature = "proptest")]
    use proptest::prelude::*;

    use std::collections::HashMap;

    use super::*;

    #[test]
    fn create_graph() {
        let graph = PortGraph::new();

        assert_eq!(graph.node_count(), 0);
        assert_eq!(graph.port_count(), 0);
        assert_eq!(graph.link_count(), 0);
        assert_eq!(graph.nodes_iter().count(), 0);
        assert_eq!(graph.ports_iter().count(), 0);
    }

    #[test]
    fn add_nodes() {
        let mut graph = PortGraph::with_capacity(5, 10);
        assert_eq!(graph.node_count(), 0);
        assert_eq!(graph.node_capacity(), 5);
        assert_eq!(graph.port_count(), 0);
        assert_eq!(graph.port_capacity(), 10);

        let lengths = [(0, 1), (0, 0), (1, 0), (2, 1), (1, 6)];
        let node_count = lengths.len();
        let port_count = lengths
            .iter()
            .map(|(incoming, outgoing)| incoming + outgoing)
            .sum();

        for (incoming, outgoing) in lengths.iter().copied() {
            let node = graph.add_node(incoming, outgoing);
            assert!(graph.contains_node(node));

            assert_eq!(graph.inputs(node).count(), incoming);
            assert_eq!(graph.outputs(node).count(), outgoing);
            assert_eq!(graph.num_ports(node, Direction::Incoming), incoming);
            assert_eq!(graph.num_ports(node, Direction::Outgoing), outgoing);
            assert_eq!(graph.all_ports(node).count(), incoming + outgoing);
            assert_eq!(graph.all_port_offsets(node).count(), incoming + outgoing);

            let inputs = graph
                .inputs(node)
                .enumerate()
                .map(|(i, port)| (i, port, Direction::Incoming));
            let outputs = graph
                .outputs(node)
                .enumerate()
                .map(|(i, port)| (i, port, Direction::Outgoing));
            for (i, port, dir) in inputs.chain(outputs) {
                let offset = PortOffset::new(dir, i);
                assert_eq!(graph.port_direction(port), Some(dir));
                assert_eq!(graph.port_offset(port), Some(offset));
                assert_eq!(graph.port_node(port), Some(node));
                assert_eq!(graph.port_index(node, offset), Some(port));
                assert_eq!(graph.port_link(port), None);
            }
        }

        // Global iterators
        let nodes = graph.nodes_iter().take(2);
        let nodes = nodes.chain(graph.nodes_iter().skip(2));
        let nodes = nodes.collect::<Vec<_>>();
        assert_eq!(
            nodes,
            (0..node_count).map(NodeIndex::new).collect::<Vec<_>>()
        );

        let ports = graph.ports_iter().take(2);
        let ports = ports.chain(graph.ports_iter().skip(2));
        let ports = ports.collect::<Vec<_>>();
        assert_eq!(ports.len(), port_count);
        assert_eq!(
            ports,
            (0..port_count).map(PortIndex::new).collect::<Vec<_>>()
        );
    }

    #[test]
    fn link_ports() {
        let mut g = PortGraph::new();
        let node0 = g.add_node(2, 1);
        let node1 = g.add_node(1, 2);
        let node0_input = g.input(node0, 0).unwrap();
        let node0_input2 = g.input(node0, 1).unwrap();
        let node0_output = g.output(node0, 0).unwrap();
        let node1_input = g.input(node1, 0).unwrap();
        let node1_output = g.output(node1, 0).unwrap();
        let node1_output2 = g.output(node1, 1).unwrap();
        assert_eq!(g.link_count(), 0);
        assert!(!g.connected(node0, node1));
        assert!(!g.connected(node1, node0));

        g.link_ports(node0_output, node1_input).unwrap();
        assert_eq!(g.link_count(), 1);
        assert_eq!(
            g.get_connections(node0, node1).collect::<Vec<_>>(),
            vec![(node0_output, node1_input)]
        );
        assert!(!g.connected(node1, node0));

        g.link_nodes(node1, 0, node0, 0).unwrap();
        assert_eq!(g.link_count(), 2);
        assert_eq!(
            g.get_connections(node0, node1).collect::<Vec<_>>(),
            vec![(node0_output, node1_input)]
        );
        assert_eq!(
            g.get_connections(node1, node0).collect::<Vec<_>>(),
            vec![(node1_output, node0_input)]
        );

        g.unlink_port(node0_output);
        assert_eq!(g.link_count(), 1);
        assert!(!g.connected(node0, node1));
        assert_eq!(
            g.get_connections(node1, node0).collect::<Vec<_>>(),
            vec![(node1_output, node0_input)]
        );

        g.link_nodes(node1, 1, node0, 1).unwrap();
        assert_eq!(g.link_count(), 2);
        assert!(!g.connected(node0, node1));
        assert_eq!(
            g.get_connections(node1, node0).collect::<Vec<_>>(),
            vec![(node1_output, node0_input), (node1_output2, node0_input2)]
        );
        assert_eq!(
            g.get_connections(node1, node0).rev().collect::<Vec<_>>(),
            vec![(node1_output2, node0_input2), (node1_output, node0_input)]
        );
    }

    #[test]
    fn link_ports_errors() {
        let mut g = PortGraph::new();
        let node0 = g.add_node(1, 1);
        let node1 = g.add_node(1, 1);
        let node0_input = g.input(node0, 0).unwrap();
        let node0_output = g.output(node0, 0).unwrap();
        let node1_input = g.input(node1, 0).unwrap();
        let node1_output = g.output(node1, 0).unwrap();
        assert!(g.link_ports(node0_input, node1_input).is_err());
        assert!(g.link_ports(node0_output, node1_output).is_err());
        g.link_ports(node0_output, node0_input).unwrap();
        assert!(g.link_ports(node0_output, node1_input).is_err());
        g.unlink_port(node0_output);
        g.remove_node(node1);
        assert!(g.link_ports(node1_output, node0_input).is_err());
    }

    #[test]
    fn link_iterators() {
        let mut g = PortGraph::new();
        let node0 = g.add_node(1, 2);
        let node1 = g.add_node(2, 1);
        let node1_input0 = g.input(node1, 0).unwrap();
        let node1_input1 = g.input(node1, 1).unwrap();

        assert!(g.input_links(node0).eq([None]));
        assert!(g.output_links(node0).eq([None, None]));
        assert!(g.all_links(node0).eq([None, None, None]));
        assert!(g.input_neighbours(node0).eq([]));
        assert!(g.output_neighbours(node0).eq([]));
        assert!(g.all_neighbours(node0).eq([]));

        g.link_nodes(node0, 0, node1, 0).unwrap();

        assert!(g.input_links(node0).eq([None]));
        assert!(g.output_links(node0).eq([Some(node1_input0), None]));
        assert!(g.all_links(node0).eq([None, Some(node1_input0), None]));
        assert!(g.input_neighbours(node0).eq([]));
        assert!(g.output_neighbours(node0).eq([node1]));
        assert!(g.all_neighbours(node0).eq([node1]));

        g.link_nodes(node0, 1, node1, 1).unwrap();

        assert!(g.input_links(node0).eq([None]));
        assert!(g
            .output_links(node0)
            .eq([Some(node1_input0), Some(node1_input1)]));
        assert!(g
            .all_links(node0)
            .eq([None, Some(node1_input0), Some(node1_input1)]));
        assert!(g.input_neighbours(node0).eq([]));
        assert!(g.output_neighbours(node0).eq([node1, node1]));
        assert!(g.all_neighbours(node0).eq([node1, node1]));
    }

    #[test]
    fn compact_operations() {
        let mut g = PortGraph::new();
        let x = g.add_node(3, 2);
        let a = g.add_node(1, 1);
        let b = g.add_node(2, 2);
        let c = g.add_node(1, 1);
        g.link_nodes(a, 0, b, 0).unwrap();
        g.link_nodes(b, 0, b, 1).unwrap();
        g.link_nodes(b, 1, c, 0).unwrap();
        g.link_nodes(c, 0, a, 0).unwrap();
        let a_input = g.input(a, 0).unwrap();
        let a_output = g.input(a, 0).unwrap();

        assert_eq!(g.link_count(), 4);
        assert_eq!(g.node_count(), 4);
        assert_eq!(g.port_count(), 13);

        g.remove_node(x);

        assert_eq!(g.link_count(), 4);
        assert_eq!(g.node_count(), 3);
        assert_eq!(g.port_count(), 8);
        assert!(g.connected(a, b));
        assert!(g.connected(b, b));
        assert!(g.connected(b, c));
        assert!(g.connected(c, a));

        let mut new_nodes = HashMap::new();
        g.compact_nodes(|old, new| {
            new_nodes.insert(old, new);
        });

        assert_eq!(
            g.nodes_iter().collect::<Vec<_>>(),
            (0..3).map(NodeIndex::new).collect::<Vec<_>>()
        );
        assert_eq!(new_nodes.len(), 3);
        assert_eq!(g.port_node(a_input), Some(new_nodes[&a]));
        assert_eq!(g.port_node(a_output), Some(new_nodes[&a]));

        let a = new_nodes[&a];
        let b = new_nodes[&b];
        let c = new_nodes[&c];

        assert_eq!(g.link_count(), 4);
        assert_eq!(g.node_count(), 3);
        assert_eq!(g.port_count(), 8);
        assert!(g.connected(a, b));
        assert!(g.connected(b, b));
        assert!(g.connected(b, c));
        assert!(g.connected(c, a));

        let mut new_ports = HashMap::new();
        g.compact_ports(|old, new| {
            new_ports.insert(old, new);
        });

        assert_eq!(
            g.ports_iter().collect::<Vec<_>>(),
            (0..8).map(PortIndex::new).collect::<Vec<_>>()
        );
        assert_eq!(new_ports.len(), 8);
        assert_eq!(g.port_node(new_ports[&a_input]), Some(a));
        assert_eq!(g.port_node(new_ports[&a_output]), Some(a));

        assert_eq!(g.link_count(), 4);
        assert_eq!(g.node_count(), 3);
        assert_eq!(g.port_count(), 8);
        assert!(g.connected(a, b));
        assert!(g.connected(b, b));
        assert!(g.connected(b, c));
        assert!(g.connected(c, a));
    }

    #[test]
    fn resize_ports() {
        let mut g = PortGraph::new();
        let x = g.add_node(3, 2);
        let a = g.add_node(1, 1);
        let b = g.add_node(2, 2);
        let c = g.add_node(1, 1);
        g.link_nodes(a, 0, b, 0).unwrap();
        g.link_nodes(b, 0, b, 1).unwrap();
        g.link_nodes(b, 1, c, 0).unwrap();
        g.link_nodes(c, 0, a, 0).unwrap();

        assert_eq!(g.link_count(), 4);
        assert_eq!(g.node_count(), 4);
        assert_eq!(g.port_count(), 13);

        g.set_num_ports(x, 0, 0, |_, _| {});

        assert_eq!(g.link_count(), 4);
        assert_eq!(g.node_count(), 4);
        assert_eq!(g.port_count(), 8);
        assert!(g.connected(a, b));
        assert!(g.connected(b, b));
        assert!(g.connected(b, c));
        assert!(g.connected(c, a));

        g.set_num_ports(a, 2, 3, |_, _| {});

        assert_eq!(g.link_count(), 4);
        assert_eq!(g.node_count(), 4);
        assert_eq!(g.port_count(), 11);
        assert!(g.connected(a, b));
        assert!(g.connected(b, b));
        assert!(g.connected(b, c));
        assert!(g.connected(c, a));

        g.set_num_ports(b, 2, 3, |_, _| {});

        assert_eq!(g.link_count(), 4);
        assert_eq!(g.node_count(), 4);
        assert_eq!(g.port_count(), 12);
        assert!(g.connected(a, b));
        assert!(g.connected(b, b));
        assert!(g.connected(b, c));
        assert!(g.connected(c, a));

        g.set_num_ports(b, 3, 2, |_, _| {});

        assert_eq!(g.link_count(), 4);
        assert_eq!(g.node_count(), 4);
        assert_eq!(g.port_count(), 12);
        assert!(g.connected(a, b));
        assert!(g.connected(b, b));
        assert!(g.connected(b, c));
        assert!(g.connected(c, a));

        g.set_num_ports(b, 2, 3, |_, _| {});

        assert_eq!(g.link_count(), 4);
        assert_eq!(g.node_count(), 4);
        assert_eq!(g.port_count(), 12);
        assert!(g.connected(a, b));
        assert!(g.connected(b, b));
        assert!(g.connected(b, c));
        assert!(g.connected(c, a));
    }

    #[cfg(feature = "serde")]
    pub fn ser_roundtrip<T: Serialize + serde::de::DeserializeOwned>(g: &T) -> T {
        let v = rmp_serde::to_vec_named(g).unwrap();
        rmp_serde::from_slice(&v[..]).unwrap()
    }
    #[cfg(feature = "serde")]
    #[cfg(feature = "proptest")]
    proptest! {
        #[test]
        fn prop_serialization(graph in gen_portgraph(100, 50, 1000)) {
            prop_assert_eq!(ser_roundtrip(&graph), graph);
        }
    }

    #[cfg(feature = "serde")]
    #[test]
    fn empty_portgraph_serialize() {
        let g = PortGraph::new();
        assert_eq!(ser_roundtrip(&g), g);
    }
}
