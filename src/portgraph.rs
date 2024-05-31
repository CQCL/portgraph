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

use crate::view::{LinkMut, PortMut};
use crate::{Direction, LinkView, NodeIndex, PortIndex, PortOffset, PortView};

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

    #[inline]
    fn alloc_node(&mut self) -> NodeIndex {
        match self.node_free {
            Some(node) => {
                let free_entry = self.node_meta[node.index()].free_entry().unwrap();
                self.node_free = free_entry.next;
                if let Some(next) = free_entry.next {
                    let next_entry = self.node_meta[next.index()].free_entry_mut().unwrap();
                    next_entry.prev = None;
                }
                node
            }
            None => {
                let index = self.node_meta.len();
                self.node_meta.push(NodeEntry::new_free(None, None));
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
        if requested == 0 {
            return NodeMeta::default();
        }

        let meta_incoming = PortEntry::Port(PortMeta::new(node, Direction::Incoming));
        let meta_outgoing = PortEntry::Port(PortMeta::new(node, Direction::Outgoing));
        let meta_empty = PortEntry::Free;
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

    #[inline]
    fn free_node(&mut self, node: NodeIndex) {
        if let Some(node_free) = self.node_free {
            let free_list = self.node_meta[node_free.index()].free_entry_mut().unwrap();
            free_list.prev = Some(node);
        }
        self.node_meta[node.index()] = NodeEntry::new_free(None, self.node_free);
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
        if size == 0 {
            return;
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
        F: FnMut(PortIndex, PortOperation),
    {
        let node_meta = self.node_meta_valid(node).expect("Node must be valid");
        let new_meta = NodeMeta::new(
            node_meta.first_port(),
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
            let old_link = self.unlink_port(port);
            rekey(port, PortOperation::Removed { old_link });
        }

        let move_port = |(old, new)| {
            let old_index = PortIndex::new(old);
            let new_index = PortIndex::new(new);
            self.port_link[new] = self.port_link[old];
            self.port_meta[new] = self.port_meta[old];
            rekey(old_index, PortOperation::Moved { new_index });
            if let Some(link) = self.port_link[new] {
                self.port_link[link.index()] = Some(new_index);
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
        for port_offset in new_meta.port_count()..node_meta.port_count() {
            let port = new_meta.first_port().index() + port_offset;
            self.port_link[port] = None;
            self.port_meta[port] = PortEntry::Free;
        }

        self.node_meta[node.index()] = NodeEntry::Node(new_meta);

        self.port_count -= node_meta.incoming() as usize + node_meta.outgoing() as usize;
        self.port_count += incoming + outgoing;
    }

    /// Returns the range of outgoing port indices for a given node.
    pub(crate) fn node_outgoing_ports(&self, node: NodeIndex) -> Range<usize> {
        match self.node_meta_valid(node) {
            Some(node_meta) => node_meta.outgoing_ports(),
            None => 0..0,
        }
    }
}

impl PortView for PortGraph {
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
        Some(self.port_meta_valid(port.into())?.direction())
    }

    #[inline]
    fn port_node(&self, port: impl Into<PortIndex>) -> Option<NodeIndex> {
        Some(self.port_meta_valid(port.into())?.node())
    }

    fn port_offset(&self, port: impl Into<PortIndex>) -> Option<PortOffset> {
        let port = port.into();
        let port_meta = self.port_meta_valid(port)?;
        let node = port_meta.node();

        let NodeEntry::Node(node_meta) = self.node_meta[node.index()] else {
            unreachable!("ports are only attached to valid nodes");
        };

        let port_offset = port.index().wrapping_sub(node_meta.first_port().index());

        match port_meta.direction() {
            Direction::Incoming => Some(PortOffset::new_incoming(port_offset)),
            Direction::Outgoing => {
                let port_offset = port_offset.saturating_sub(node_meta.incoming() as usize);
                Some(PortOffset::new_outgoing(port_offset))
            }
        }
    }

    fn port_index(&self, node: NodeIndex, offset: PortOffset) -> Option<PortIndex> {
        let node_meta = self.node_meta_valid(node)?;
        let direction = offset.direction();
        let offset = offset.index();
        node_meta.ports(direction).nth(offset).map(PortIndex::new)
    }

    fn ports(&self, node: NodeIndex, direction: Direction) -> Self::NodePorts<'_> {
        match self.node_meta_valid(node) {
            Some(node_meta) => NodePorts {
                indices: node_meta.ports(direction),
            },
            None => NodePorts::default(),
        }
    }

    fn all_ports(&self, node: NodeIndex) -> Self::NodePorts<'_> {
        match self.node_meta_valid(node) {
            Some(node_meta) => NodePorts {
                indices: node_meta.all_ports(),
            },
            None => NodePorts::default(),
        }
    }

    #[inline]
    fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.port_index(node, PortOffset::new_incoming(offset))
    }

    #[inline]
    fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.port_index(node, PortOffset::new_outgoing(offset))
    }

    fn num_ports(&self, node: NodeIndex, direction: Direction) -> usize {
        let Some(node_meta) = self.node_meta_valid(node) else {
            return 0;
        };
        if Direction::Incoming == direction {
            node_meta.incoming() as usize
        } else {
            node_meta.outgoing() as usize
        }
    }

    fn port_offsets(&self, node: NodeIndex, direction: Direction) -> Self::NodePortOffsets<'_> {
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

    #[inline]
    fn all_port_offsets(&self, node: NodeIndex) -> Self::NodePortOffsets<'_> {
        NodePortOffsets {
            incoming: 0..self.num_inputs(node) as u16,
            outgoing: 0..self.num_outputs(node) as u32,
        }
    }

    #[inline]
    fn contains_node(&self, node: NodeIndex) -> bool {
        self.node_meta_valid(node).is_some()
    }

    #[inline]
    fn contains_port(&self, port: PortIndex) -> bool {
        self.port_meta_valid(port).is_some()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.node_count == 0 && self.port_count == 0
    }

    #[inline]
    fn node_count(&self) -> usize {
        self.node_count
    }

    #[inline]
    fn port_count(&self) -> usize {
        self.port_count
    }

    #[inline]
    fn nodes_iter(&self) -> Self::Nodes<'_> {
        Nodes {
            iter: self.node_meta.iter().enumerate(),
            len: self.node_count,
        }
    }

    #[inline]
    fn ports_iter(&self) -> Self::Ports<'_> {
        Ports {
            iter: self.port_meta.iter().enumerate(),
            len: self.port_count,
        }
    }

    #[inline]
    fn node_capacity(&self) -> usize {
        self.node_meta.capacity()
    }

    #[inline]
    fn port_capacity(&self) -> usize {
        self.port_meta.capacity()
    }

    #[inline]
    fn node_port_capacity(&self, node: NodeIndex) -> usize {
        self.node_meta_valid(node)
            .map_or(0, |node_meta| node_meta.capacity())
    }
}

impl PortMut for PortGraph {
    fn add_node(&mut self, incoming: usize, outgoing: usize) -> NodeIndex {
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

    fn remove_node(&mut self, node: NodeIndex) {
        let Some(node_meta) = self.node_meta.get(node.index()).copied() else {
            return;
        };

        let NodeEntry::Node(node_meta) = node_meta else {
            return;
        };

        self.free_node(node);

        self.node_count -= 1;

        if node_meta.capacity() > 0 {
            let first_port = node_meta.first_port();
            let size = node_meta.capacity();
            self.port_count -= node_meta.port_count();

            assert!(first_port.index() + size <= self.port_link.len());
            assert!(first_port.index() + size <= self.port_meta.len());

            self.free_ports(first_port, size);
        }
    }

    fn clear(&mut self) {
        self.node_meta.clear();
        self.port_link.clear();
        self.port_meta.clear();
        self.node_free = None;
        self.port_free.clear();
        self.node_count = 0;
        self.port_count = 0;
        self.link_count = 0;
    }

    fn reserve(&mut self, nodes: usize, ports: usize) {
        self.node_meta.reserve(nodes);
        self.port_meta.reserve(ports);
        self.port_link.reserve(ports);
    }

    fn set_num_ports<F>(&mut self, node: NodeIndex, incoming: usize, outgoing: usize, mut rekey: F)
    where
        F: FnMut(PortIndex, PortOperation),
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

        let Some(node_meta) = self.node_meta_valid(node) else {
            return;
        };
        let old_incoming = node_meta.incoming() as usize;
        let old_outgoing = node_meta.outgoing() as usize;
        let old_capacity = node_meta.capacity();
        let old_total = old_incoming + old_outgoing;
        let old_first_port = node_meta.first_port();
        if old_incoming == incoming && old_outgoing == outgoing {
            // Nothing to do
            return;
        } else if (1..old_capacity).contains(&new_total) {
            // Special case when we can avoid reallocations by shifting the
            // ports in the pre-allocated slab.
            self.resize_ports_inplace(node, incoming, outgoing, rekey);
            return;
        }

        // Disconnect any port to be removed.
        for port in self
            .inputs(node)
            .skip(incoming)
            .chain(self.outputs(node).skip(outgoing))
        {
            let old_link = self.unlink_port(port);
            rekey(port, PortOperation::Removed { old_link });
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

                let new_index = PortIndex::new(new);
                rekey(PortIndex::new(old), PortOperation::Moved { new_index });
            }
        }

        self.node_meta[node.index()] = NodeEntry::Node(new_meta);
        self.free_ports(old_first_port, old_capacity);

        self.port_count = self.port_count - old_total + new_total;
    }

    fn compact_nodes<F>(&mut self, mut rekey: F)
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

    fn swap_nodes(&mut self, a: NodeIndex, b: NodeIndex) {
        let meta_a = self.node_meta[a.index()];
        let meta_b = self.node_meta[b.index()];
        self.node_meta.swap(a.index(), b.index());
        // Update the node indices in the ports metadata.
        let mut update_ports = |new_node: NodeIndex, entry: NodeEntry| {
            let NodeEntry::Node(node_meta) = entry else {
                return;
            };
            for dir in Direction::BOTH {
                for port in node_meta.ports(dir) {
                    self.port_meta[port] = PortEntry::Port(PortMeta::new(new_node, dir));
                }
            }
        };
        update_ports(a, meta_b);
        update_ports(b, meta_a);
        // Update the free node linked list, only if we swapping empty and
        // non-empty spaces.
        let mut update_free_list = |new_node: NodeIndex, entry: FreeNodeEntry| {
            if let Some(prev) = entry.prev {
                self.node_meta[prev.index()].free_entry_mut().unwrap().next = Some(new_node);
            }
            if let Some(next) = entry.next {
                self.node_meta[next.index()].free_entry_mut().unwrap().prev = Some(new_node);
            }
        };
        match (meta_a, meta_b) {
            (NodeEntry::Free(meta_a), NodeEntry::Node(_)) => update_free_list(b, meta_a),
            (NodeEntry::Node(_), NodeEntry::Free(meta_b)) => update_free_list(a, meta_b),
            _ => (),
        }
    }

    fn compact_ports<F>(&mut self, mut rekey: F)
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
            if node_meta.first_port() == old_port {
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

    fn shrink_to_fit(&mut self) {
        self.node_meta.shrink_to_fit();
        self.port_link.shrink_to_fit();
        self.port_meta.shrink_to_fit();
        self.port_free.shrink_to_fit();
    }
}

impl LinkView for PortGraph {
    type LinkEndpoint = PortIndex;

    type Neighbours<'a> = Neighbours<'a>
    where
        Self: 'a;

    type NodeConnections<'a> = NodeConnections<'a>
    where
        Self: 'a;

    type NodeLinks<'a> = NodeLinks<'a>
    where
        Self: 'a;

    type PortLinks<'a> = std::iter::Once<(PortIndex, PortIndex)>
    where
        Self: 'a;

    #[inline]
    fn get_connections(&self, from: NodeIndex, to: NodeIndex) -> Self::NodeConnections<'_> {
        NodeConnections::new(self, to, self.output_links(from))
    }

    fn port_links(&self, port: PortIndex) -> Self::PortLinks<'_> {
        self.port_meta_valid(port).unwrap();
        match self.port_link[port.index()] {
            Some(link) => std::iter::once((port, link)),
            None => {
                let mut iter = std::iter::once((port, port));
                iter.next();
                iter
            }
        }
    }

    fn links(&self, node: NodeIndex, direction: Direction) -> Self::NodeLinks<'_> {
        let Some(node_meta) = self.node_meta_valid(node) else {
            return NodeLinks::new(self.ports(node, direction), &[], 0..0);
        };
        let indices = node_meta.ports(direction);
        NodeLinks::new(self.ports(node, direction), &self.port_link[indices], 0..0)
    }

    fn all_links(&self, node: NodeIndex) -> Self::NodeLinks<'_> {
        let Some(node_meta) = self.node_meta_valid(node) else {
            return NodeLinks::new(self.all_ports(node), &[], 0..0);
        };
        let indices = node_meta.all_ports();
        // Ignore links where the target is one of the node's output ports.
        // This way we only count self-links once.
        NodeLinks::new(
            self.all_ports(node),
            &self.port_link[indices],
            node_meta.outgoing_ports(),
        )
    }

    #[inline]
    fn neighbours(&self, node: NodeIndex, direction: Direction) -> Self::Neighbours<'_> {
        Neighbours::from_node_links(self, self.links(node, direction))
    }

    #[inline]
    fn all_neighbours(&self, node: NodeIndex) -> Self::Neighbours<'_> {
        Neighbours::from_node_links(self, self.all_links(node))
    }

    #[inline]
    fn link_count(&self) -> usize {
        self.link_count
    }
}

impl LinkMut for PortGraph {
    fn link_ports(
        &mut self,
        port_a: PortIndex,
        port_b: PortIndex,
    ) -> Result<(Self::LinkEndpoint, Self::LinkEndpoint), LinkError> {
        let Some(meta_a) = self.port_meta_valid(port_a) else {
            return Err(LinkError::UnknownPort { port: port_a });
        };

        let Some(meta_b) = self.port_meta_valid(port_b) else {
            return Err(LinkError::UnknownPort { port: port_a });
        };

        if meta_a.direction() == meta_b.direction() {
            return Err(LinkError::IncompatibleDirections {
                port_a,
                port_b,
                dir: meta_a.direction(),
            });
        }

        if self.port_link[port_a.index()].is_some() {
            return Err(LinkError::AlreadyLinked { port: port_a });
        } else if self.port_link[port_b.index()].is_some() {
            return Err(LinkError::AlreadyLinked { port: port_b });
        }

        self.port_link[port_a.index()] = Some(port_b);
        self.port_link[port_b.index()] = Some(port_a);
        self.link_count += 1;
        Ok((port_a, port_b))
    }

    fn unlink_port(&mut self, port: PortIndex) -> Option<PortIndex> {
        self.port_meta_valid(port)?;
        let linked = take(&mut self.port_link[port.index()])?;
        self.port_link[linked.index()] = None;
        self.link_count -= 1;
        Some(linked)
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
    first_port: PortIndex,
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
    pub fn new(first_port: PortIndex, incoming: u16, outgoing: u16, capacity: u16) -> Self {
        assert!(incoming <= Self::MAX_INCOMING as u16);
        assert!(outgoing <= Self::MAX_OUTGOING as u16);
        assert!(incoming.saturating_add(outgoing) <= capacity);
        assert!(capacity > 0 || first_port.index() == 0);
        Self {
            first_port,
            // SAFETY: The value cannot be zero, and won't overflow.
            incoming: unsafe { NonZeroU16::new_unchecked(incoming + 1) },
            outgoing,
            capacity,
        }
    }

    #[inline]
    pub fn first_port(&self) -> PortIndex {
        self.first_port
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
        let start = self.first_port.index();
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
        let start = self.first_port.index();
        let end = start + self.incoming() as usize;
        start..end
    }

    /// Returns a range over the outgoing port indices of this node.
    #[inline]
    pub fn outgoing_ports(&self) -> Range<usize> {
        let start = self.first_port.index() + self.incoming() as usize;
        let end = start + self.outgoing() as usize;
        start..end
    }

    /// Returns a range over the unused pre-allocated port indices of this node.
    #[inline]
    pub fn unused_ports(&self) -> Range<usize> {
        let start = self.first_port.index() + self.port_count();
        let end = self.first_port.index() + self.capacity();
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
    /// Instead the entry forms a doubly-linked list of free nodes.
    #[cfg_attr(feature = "serde", serde(rename = "f",))]
    Free(FreeNodeEntry),
    /// A node is stored at this entry.
    ///
    /// This value allows for null-value optimization so that
    /// `size_of::<NodeEntry>() == size_of::<NodeMeta>()`.
    #[cfg_attr(feature = "serde", serde(rename = "n"))]
    Node(NodeMeta),
}

impl NodeEntry {
    /// Returns the free node list entry.
    #[inline]
    pub fn free_entry(&self) -> Option<&FreeNodeEntry> {
        match self {
            NodeEntry::Free(entry) => Some(entry),
            NodeEntry::Node(_) => None,
        }
    }

    /// Returns the free node list entry.
    #[inline]
    pub fn free_entry_mut(&mut self) -> Option<&mut FreeNodeEntry> {
        match self {
            NodeEntry::Free(entry) => Some(entry),
            NodeEntry::Node(_) => None,
        }
    }

    /// Create a new free node entry
    #[inline]
    pub fn new_free(prev: Option<NodeIndex>, next: Option<NodeIndex>) -> Self {
        NodeEntry::Free(FreeNodeEntry { prev, next })
    }
}

/// Metadata for a free node space.
///
/// The entry forms a doubly-linked list of free nodes.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
struct FreeNodeEntry {
    /// The previous free node.
    prev: Option<NodeIndex>,
    /// The next free node.
    next: Option<NodeIndex>,
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
            let inputs = PortRangeDebug(self.0.inputs(self.1).as_range());
            let outputs = PortRangeDebug(self.0.outputs(self.1).as_range());

            f.debug_struct("Node")
                .field("inputs", &inputs)
                .field("outputs", &outputs)
                .finish()
        }
    }

    pub struct PortRangeDebug(pub Range<usize>);

    impl std::fmt::Debug for PortRangeDebug {
        fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if self.0.is_empty() {
                write!(fmt, "[]")?;
            } else if self.0.len() == 1 {
                write!(fmt, "[")?;
                PortIndex::new(self.0.start).fmt(fmt)?;
                write!(fmt, "]")?;
            } else {
                PortIndex::new(self.0.start).fmt(fmt)?;
                write!(fmt, "..")?;
                PortIndex::new(self.0.end).fmt(fmt)?;
            }
            Ok(())
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
    /// The ports have the same direction so they cannot be linked.
    #[error("Cannot link two ports with direction {dir:?}. In ports {port_a:?} and {port_b:?}")]
    IncompatibleDirections {
        port_a: PortIndex,
        port_b: PortIndex,
        dir: Direction,
    },
}

/// Operations applied to a port, used by the callback in [`PortGraph::set_num_ports`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PortOperation {
    /// The port was moved to a new position.
    Moved {
        /// New index for the port
        new_index: PortIndex,
    },
    /// The port was removed.
    Removed {
        /// The old link from the port, if any.
        old_link: Option<PortIndex>,
    },
}

impl PortOperation {
    /// Return the new index of the port, if it was moved
    pub fn new_index(&self) -> Option<PortIndex> {
        match self {
            PortOperation::Moved { new_index } => Some(*new_index),
            _ => None,
        }
    }
}

#[cfg(test)]
pub mod test {
    #[cfg(feature = "serde")]
    #[cfg(feature = "proptest")]
    use crate::proptest::gen_portgraph;
    use itertools::Itertools;
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
        let node0 = g.add_node(1, 3);
        let node1 = g.add_node(2, 1);
        let node0_input0 = g.input(node0, 0).unwrap();
        let node0_output0 = g.output(node0, 0).unwrap();
        let node0_output1 = g.output(node0, 1).unwrap();
        let node0_output2 = g.output(node0, 2).unwrap();
        let node1_input0 = g.input(node1, 0).unwrap();
        let node1_input1 = g.input(node1, 1).unwrap();

        assert!(g.input_links(node0).eq([]));
        assert!(g.output_links(node0).eq([]));
        assert!(g.all_links(node0).eq([]));
        assert!(g.input_neighbours(node0).eq([]));
        assert!(g.output_neighbours(node0).eq([]));
        assert!(g.all_neighbours(node0).eq([]));

        g.link_nodes(node0, 0, node1, 0).unwrap();

        assert!(g.input_links(node0).eq([]));
        assert!(g.output_links(node0).eq([(node0_output0, node1_input0)]));
        assert!(g.all_links(node0).eq([(node0_output0, node1_input0)]));
        assert!(g.input_neighbours(node0).eq([]));
        assert!(g.output_neighbours(node0).eq([node1]));
        assert!(g.all_neighbours(node0).eq([node1]));

        g.link_nodes(node0, 1, node1, 1).unwrap();

        assert!(g.input_links(node0).eq([]));
        assert!(g
            .output_links(node0)
            .eq([(node0_output0, node1_input0), (node0_output1, node1_input1)]));
        assert!(g
            .all_links(node0)
            .eq([(node0_output0, node1_input0), (node0_output1, node1_input1)]));
        assert!(g.input_neighbours(node0).eq([]));
        assert!(g.output_neighbours(node0).eq([node1, node1]));
        assert!(g.all_neighbours(node0).eq([node1, node1]));

        // Self-link
        g.link_nodes(node0, 2, node0, 0).unwrap();

        assert!(g.input_links(node0).eq([(node0_input0, node0_output2)]));
        assert!(g.output_links(node0).eq([
            (node0_output0, node1_input0),
            (node0_output1, node1_input1),
            (node0_output2, node0_input0)
        ]));
        // The self-link should only appear once in the all_links iterator
        assert!(g.all_links(node0).eq([
            (node0_output0, node1_input0),
            (node0_output1, node1_input1),
            (node0_output2, node0_input0)
        ]));
        assert!(g.input_neighbours(node0).eq([node0]));
        assert!(g.output_neighbours(node0).eq([node1, node1, node0]));
        assert!(g.all_neighbours(node0).eq([node1, node1, node0]));
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

        g.set_num_ports(x, 0, 3, |_, _| {});

        assert_eq!(g.link_count(), 4);
        assert_eq!(g.node_count(), 4);
        assert_eq!(g.port_count(), 11);
        assert!(g.connected(a, b));
        assert!(g.connected(b, b));
        assert!(g.connected(b, c));
        assert!(g.connected(c, a));

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

        // Grow an empty node
        let d = g.add_node(0, 0);
        g.set_num_ports(d, 2, 3, |_, _| {});
        assert_eq!(g.port_count(), 17);
        g.set_num_ports(d, 0, 0, |_, _| {});
        assert_eq!(g.port_count(), 12);

        // Check links after resizing
        g.clear();
        let n0 = g.add_node(0, 2);
        let n1 = g.add_node(2, 1);
        g.link_nodes(n0, 0, n1, 0).unwrap();

        g.set_num_ports(n1, 1, 1, |_, _| {});

        let o = g.output(n0, 0).unwrap();
        let i = g.port_link(o).unwrap();
        assert!(g.port_node(i).is_some());
    }

    #[test]
    fn insert_graph() -> Result<(), Box<dyn std::error::Error>> {
        let mut g = PortGraph::new();
        // Add dummy nodes to produce different node ids than in the other graph.
        g.add_node(0, 0);
        g.add_node(0, 0);
        let node0g = g.add_node(1, 1);
        let node1g = g.add_node(1, 1);
        g.link_nodes(node0g, 0, node1g, 0)?;

        let mut h = PortGraph::new();
        let node0h = h.add_node(2, 2);
        let node1h = h.add_node(1, 1);
        h.link_nodes(node0h, 0, node1h, 0)?;
        h.link_nodes(node0h, 1, node0h, 0)?;
        h.link_nodes(node1h, 0, node0h, 1)?;

        let map = g.insert_graph(&h)?;
        assert_eq!(map.len(), 2);

        assert_eq!(g.node_count(), 6);
        assert_eq!(g.link_count(), 4);
        assert!(g.contains_node(map[&node0h]));
        assert!(g.contains_node(map[&node1h]));
        assert_eq!(
            g.input_neighbours(map[&node0h]).collect_vec(),
            [map[&node0h], map[&node1h]]
        );
        assert_eq!(
            g.output_neighbours(map[&node0h]).collect_vec(),
            [map[&node1h], map[&node0h]]
        );
        assert_eq!(
            g.all_neighbours(map[&node0h]).collect_vec(),
            [map[&node1h], map[&node1h], map[&node0h]]
        );

        Ok(())
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
