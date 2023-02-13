use std::{
    iter::FusedIterator,
    mem::{replace, take},
    num::NonZeroU32,
};

use crate::{graph::Direction, NodeIndex, PortIndex};
use thiserror::Error;

#[derive(Clone)]
pub struct PortGraph {
    node_meta: Vec<NodeMeta>,
    port_link: Vec<Option<PortIndex>>,
    port_meta: Vec<PortMeta>,
    node_free: Option<NodeIndex>,
    port_free: Vec<Option<PortIndex>>,
    node_count: usize,
    port_count: usize,
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
        }
    }

    /// Adds a node to the portgraph with a given number of input and output ports.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::portgraph::PortGraph;
    /// # use portgraph::graph::Direction;
    /// let mut g = PortGraph::new();
    /// let node = g.add_node(4, 3);
    /// assert_eq!(g.inputs(node).count(), 4);
    /// assert_eq!(g.outputs(node).count(), 3);
    /// assert!(g.contains_node(node));
    /// ```
    pub fn add_node(&mut self, incoming: usize, outgoing: usize) -> NodeIndex {
        let node = self.alloc_node();

        let port_list = if incoming + outgoing > 0 {
            Some(self.alloc_ports(node, incoming, outgoing))
        } else {
            None
        };

        self.node_meta[node.index()] =
            NodeMeta::new_node(port_list, incoming as u16, outgoing as u16);

        self.node_count += 1;
        self.port_count += incoming + outgoing;

        node
    }

    #[inline]
    fn alloc_node(&mut self) -> NodeIndex {
        match self.node_free {
            Some(node) => {
                let meta_before = self.node_meta[node.index()];
                debug_assert!(meta_before.is_free());
                self.node_free = meta_before.free_next();
                node
            }
            None => {
                let index = self.node_meta.len();
                self.node_meta.push(NodeMeta::new_free(None));
                NodeIndex::new(index)
            }
        }
    }

    #[inline]
    fn alloc_ports(&mut self, node: NodeIndex, incoming: usize, outgoing: usize) -> PortIndex {
        let size = incoming + outgoing;
        let meta_incoming = PortMeta::new_node(node, Direction::Incoming);
        let meta_outgoing = PortMeta::new_node(node, Direction::Outgoing);

        match self.port_free.get(size - 1).copied().flatten() {
            Some(port) => {
                let free_next = take(&mut self.port_link[port.index()]);
                debug_assert!(self.port_meta[port.index()].is_free());
                self.port_free[size - 1] = free_next;

                let i = port.index();
                self.port_meta[(i + incoming..i + size)].fill(meta_outgoing);
                self.port_meta[(i..i + incoming)].fill(meta_incoming);
                self.port_link[(i..i + size)].fill(None);

                port
            }
            None => {
                debug_assert_eq!(self.port_meta.len(), self.port_link.len());
                let old_len = self.port_meta.len();
                let port = PortIndex::new(old_len);

                self.port_meta.reserve(size);
                self.port_meta.resize(old_len + incoming, meta_incoming);
                self.port_meta.resize(old_len + size, meta_outgoing);
                self.port_link.resize(old_len + size, None);

                port
            }
        }
    }

    /// Remove a node from the port graph. All ports of the node will be
    /// unlinked and removed as well. Does nothing if the node does not exist.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::portgraph::PortGraph;
    /// # use portgraph::graph::Direction;
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

        if node_meta.is_free() {
            return;
        }

        self.free_node(node);

        self.node_count -= 1;

        if let Some(port_list) = node_meta.port_list() {
            let size = node_meta.incoming() as usize + node_meta.outgoing() as usize;
            self.port_count -= size;

            assert!(port_list.index() + size <= self.port_link.len());
            assert!(port_list.index() + size <= self.port_meta.len());

            for i in port_list.index()..port_list.index() + size {
                self.port_meta[i] = PortMeta::new_free();

                if let Some(link) = self.port_link[i] {
                    self.port_link[link.index()] = None;
                }
            }

            self.free_ports(port_list, size);
        }
    }

    #[inline]
    fn free_node(&mut self, node: NodeIndex) {
        let meta_before = replace(
            &mut self.node_meta[node.index()],
            NodeMeta::new_free(self.node_free),
        );

        debug_assert!(!meta_before.is_free());
        self.node_free = Some(node);
    }

    #[inline]
    fn free_ports(&mut self, ports: PortIndex, size: usize) {
        if size > self.port_free.len() {
            self.port_free.resize(size, None);
        }

        let ports_free = &mut self.port_free[size - 1];

        self.port_meta[ports.index()] = PortMeta::new_free();
        self.port_link[ports.index()] = replace(ports_free, Some(ports));
    }

    /// Link an output port to an input port.
    ///
    /// # Example
    ///
    /// ```
    /// # use portgraph::portgraph::PortGraph;
    /// # use portgraph::graph::Direction;
    /// let mut g = PortGraph::new();
    /// let node0 = g.add_node(0, 1);
    /// let node1 = g.add_node(1, 0);
    /// let node0_output = g.outputs(node0).nth(0).unwrap();
    /// let node1_input = g.inputs(node1).nth(0).unwrap();
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
            return Err(LinkError::UnknownPort(port_from));
        };

        let Some(meta_to) = self.port_meta_valid(port_to) else {
            return Err(LinkError::UnknownPort(port_from));
        };

        if meta_from.direction() != Direction::Outgoing {
            return Err(LinkError::UnexpectedDirection(port_from));
        } else if meta_to.direction() != Direction::Incoming {
            return Err(LinkError::UnexpectedDirection(port_to));
        }

        if self.port_link[port_from.index()].is_some() {
            return Err(LinkError::AlreadyLinked(port_from));
        } else if self.port_link[port_to.index()].is_some() {
            return Err(LinkError::AlreadyLinked(port_to));
        }

        self.port_link[port_from.index()] = Some(port_to);
        self.port_link[port_to.index()] = Some(port_from);

        Ok(())
    }

    /// Unlinks the `port` and returns the port it was linked to. Returns `None`
    /// when the port was not linked.
    pub fn unlink_port(&mut self, port: PortIndex) -> Option<PortIndex> {
        self.port_meta_valid(port)?;
        let linked = take(&mut self.port_link[port.index()])?;
        self.port_link[linked.index()] = None;
        Some(linked)
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
    pub fn port_index(&self, port: PortIndex) -> Option<usize> {
        let port_meta = self.port_meta_valid(port)?;
        let node = port_meta.node();
        // PERFORMANCE: The bounds check here is not needed
        let node_meta = self.node_meta[node.index()];
        // PERFORMANCE: The unwrap will always succeed
        let port_list = node_meta.port_list().unwrap();

        let port_offset = port.index().wrapping_sub(port_list.index());

        let port_index = port_offset
            .checked_sub(node_meta.incoming() as usize)
            .unwrap_or(port_offset);

        Some(port_index)
    }

    /// Returns the port that the given `port` is linked to.
    #[inline]
    pub fn port_link(&self, port: PortIndex) -> Option<PortIndex> {
        self.port_meta_valid(port)?;
        self.port_link[port.index()]
    }

    /// Iterates over all the ports of the `node` in the given `direction`.
    pub fn ports(&self, node: NodeIndex, direction: Direction) -> NodePorts {
        let Some(node_meta) = self.node_meta_valid(node) else {
            return NodePorts::default();
        };

        let Some(port_list) = node_meta.port_list() else {
            return NodePorts::default();
        };

        match direction {
            Direction::Incoming => NodePorts {
                index: port_list.0,
                length: node_meta.incoming() as usize,
            },
            Direction::Outgoing => NodePorts {
                index: port_list.0.saturating_add(node_meta.incoming() as u32),
                length: node_meta.outgoing() as usize,
            },
        }
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

    pub fn links(&self, node: NodeIndex, direction: Direction) -> &[Option<PortIndex>] {
        let Some(node_meta) = self.node_meta_valid(node) else {
            return &[];
        };

        let Some(port_list) = node_meta.port_list() else {
            return &[];
        };

        match direction {
            Direction::Incoming => {
                let start = port_list.index();
                let stop = start + node_meta.incoming() as usize;
                &self.port_link[start..stop]
            }
            Direction::Outgoing => {
                let start = port_list.index() + node_meta.incoming() as usize;
                let stop = start + node_meta.outgoing() as usize;
                &self.port_link[start..stop]
            }
        }
    }

    #[inline]
    pub fn input_links(&self, node: NodeIndex) -> &[Option<PortIndex>] {
        self.links(node, Direction::Incoming)
    }

    #[inline]
    pub fn output_links(&self, node: NodeIndex) -> &[Option<PortIndex>] {
        self.links(node, Direction::Outgoing)
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

    /// Reserves enough capacity to insert at least the given number of additional nodes and ports.
    ///
    /// This method does not take into account the length of the free list and might overallocate speculatively.
    pub fn reserve(&mut self, nodes: usize, ports: usize) {
        self.node_meta.reserve(nodes);
        self.port_meta.reserve(ports);
        self.port_link.reserve(ports);
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
            if node_meta.is_free() {
                old_index += 1;
                return false;
            }

            let old_node = NodeIndex::new(old_index);
            let new_node = NodeIndex::new(new_index);

            if let Some(port_list) = node_meta.port_list() {
                let incoming = node_meta.incoming() as usize;
                let outgoing = node_meta.outgoing() as usize;

                for port in port_list.index()..port_list.index() + incoming {
                    self.port_meta[port] = PortMeta::new_node(new_node, Direction::Incoming);
                }

                for port in port_list.index() + incoming..port_list.index() + outgoing {
                    self.port_meta[port] = PortMeta::new_node(new_node, Direction::Outgoing);
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
    /// Every time a port is moved, the `rekey` function will be called with is old and new index.
    pub fn compact_ports<F>(&mut self, mut rekey: F)
    where
        F: FnMut(PortIndex, PortIndex),
    {
        let mut old_index = 0;

        self.port_link.retain(|_| {
            let retain = !self.port_meta[old_index].is_free();
            old_index += 1;
            retain
        });

        let mut new_index = 0;
        let mut old_index = 0;

        self.port_meta.retain(|port_meta| {
            if port_meta.is_free() {
                old_index += 1;
                return false;
            }

            let old_port = PortIndex::new(old_index);
            let new_port = PortIndex::new(new_index);

            // If we are moving the first port in a node's port list, we have to update the node.
            let node_meta = &mut self.node_meta[port_meta.node().index()];

            if node_meta.port_list() == Some(old_port) {
                *node_meta =
                    NodeMeta::new_node(Some(new_port), node_meta.incoming(), node_meta.outgoing());
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
        let node_meta = self.node_meta.get(node.index())?;

        if node_meta.is_free() {
            None
        } else {
            Some(*node_meta)
        }
    }

    #[inline]
    #[must_use]
    fn port_meta_valid(&self, port: PortIndex) -> Option<PortMeta> {
        let port_meta = self.port_meta.get(port.index())?;

        if port_meta.is_free() {
            None
        } else {
            Some(*port_meta)
        }
    }
}

impl Default for PortGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy)]
struct NodeMeta(u32, u16, u16);

impl NodeMeta {
    #[inline]
    pub fn is_free(self) -> bool {
        self.2 == u16::MAX
    }

    #[inline]
    pub fn new_free(next: Option<NodeIndex>) -> Self {
        Self(next.map_or(0, |next| u32::from(next.0)), 0, u16::MAX)
    }

    #[inline]
    pub fn new_node(port_list: Option<PortIndex>, incoming: u16, outgoing: u16) -> Self {
        Self(
            port_list.map_or(0, |next| u32::from(next.0)),
            incoming,
            outgoing,
        )
    }

    #[inline]
    pub fn free_next(self) -> Option<NodeIndex> {
        debug_assert!(self.is_free());
        Some(NodeIndex(NonZeroU32::new(self.0)?))
    }

    #[inline]
    pub fn incoming(self) -> u16 {
        debug_assert!(!self.is_free());
        self.1
    }

    #[inline]
    pub fn outgoing(self) -> u16 {
        debug_assert!(!self.is_free());
        self.2
    }

    #[inline]
    pub fn port_list(self) -> Option<PortIndex> {
        debug_assert!(!self.is_free());
        Some(PortIndex(NonZeroU32::new(self.0)?))
    }
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

#[derive(Debug, Clone, Copy)]
struct PortMeta(u32);

impl PortMeta {
    const DIRECTION_BIT: u32 = u32::BITS - 1;
    const NODE_MASK: u32 = !(1 << Self::DIRECTION_BIT);

    #[inline]
    pub fn new_free() -> Self {
        Self(u32::MAX)
    }

    #[inline]
    pub fn new_node(node: NodeIndex, direction: Direction) -> Self {
        let direction = (direction as u32) << Self::DIRECTION_BIT;
        let index = node.index() as u32 + 1;
        Self(index | direction)
    }

    #[inline]
    pub fn is_free(self) -> bool {
        self.0 == u32::MAX
    }

    #[inline]
    pub fn direction(self) -> Direction {
        debug_assert!(!self.is_free());
        if self.0 >> Self::DIRECTION_BIT == 0 {
            Direction::Incoming
        } else {
            Direction::Outgoing
        }
    }

    #[inline]
    pub fn node(self) -> NodeIndex {
        debug_assert!(!self.is_free());
        match NonZeroU32::new(self.0 & Self::NODE_MASK) {
            Some(index) => NodeIndex(index),
            None => panic!(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct NodePorts {
    index: NonZeroU32,
    length: usize,
}

impl Iterator for NodePorts {
    type Item = PortIndex;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.length = self.length.checked_sub(1)?;
        let port = PortIndex(self.index);
        // can never saturate
        self.index = self.index.saturating_add(1);
        Some(port)
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.length = self.length.checked_sub(n)?;
        let index = self.index.saturating_add(n as u32);
        self.index = index.saturating_add(1);
        Some(PortIndex(index))
    }

    fn count(self) -> usize {
        self.length
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.length, Some(self.length))
    }
}

impl ExactSizeIterator for NodePorts {
    fn len(&self) -> usize {
        self.length
    }
}

impl FusedIterator for NodePorts {}

impl Default for NodePorts {
    fn default() -> Self {
        Self {
            index: NonZeroU32::new(1).unwrap(),
            length: 0,
        }
    }
}

#[derive(Clone)]
pub struct Nodes<'a> {
    iter: std::iter::Enumerate<std::slice::Iter<'a, NodeMeta>>,
    len: usize,
}

impl<'a> Iterator for Nodes<'a> {
    type Item = NodeIndex;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.find_map(|(index, node_meta)| {
            if !node_meta.is_free() {
                self.len -= 1;
                Some(NodeIndex::new(index))
            } else {
                None
            }
        })
    }

    fn count(self) -> usize {
        self.len
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a> ExactSizeIterator for Nodes<'a> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a> DoubleEndedIterator for Nodes<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        while let Some((index, node_meta)) = self.iter.next_back() {
            if !node_meta.is_free() {
                self.len -= 1;
                return Some(NodeIndex::new(index));
            }
        }

        None
    }
}

impl<'a> FusedIterator for Nodes<'a> {}

#[derive(Clone)]
pub struct Ports<'a> {
    iter: std::iter::Enumerate<std::slice::Iter<'a, PortMeta>>,
    len: usize,
}

impl<'a> Iterator for Ports<'a> {
    type Item = PortIndex;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        for (index, port_meta) in &mut self.iter {
            if !port_meta.is_free() {
                self.len -= 1;
                return Some(PortIndex::new(index));
            }
        }

        None
    }

    fn count(self) -> usize {
        self.len
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a> ExactSizeIterator for Ports<'a> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a> DoubleEndedIterator for Ports<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        while let Some((index, port_meta)) = self.iter.next_back() {
            if !port_meta.is_free() {
                self.len -= 1;
                return Some(PortIndex::new(index));
            }
        }

        None
    }
}

impl<'a> FusedIterator for Ports<'a> {}

#[derive(Debug, Clone, Error)]
pub enum LinkError {
    #[error("port is already linked")]
    AlreadyLinked(PortIndex),
    #[error("unknown port")]
    UnknownPort(PortIndex),
    #[error("unexpected port direction")]
    UnexpectedDirection(PortIndex),
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn add_nodes() {
        let mut graph = PortGraph::new();

        let lengths = [(0, 1), (0, 0), (1, 0), (2, 1), (1, 6)];

        for (incoming, outgoing) in lengths {
            let node = graph.add_node(incoming, outgoing);
            assert!(graph.contains_node(node));
            assert_eq!(graph.ports(node, Direction::Incoming).count(), incoming);
            assert_eq!(graph.ports(node, Direction::Outgoing).count(), outgoing);
        }
    }

    #[test]
    fn link_ports_errors() {
        let mut g = PortGraph::new();
        let node0 = g.add_node(1, 1);
        let node1 = g.add_node(1, 1);
        let node0_input = g.inputs(node0).nth(0).unwrap();
        let node0_output = g.outputs(node0).nth(0).unwrap();
        let node1_input = g.inputs(node1).nth(0).unwrap();
        let node1_output = g.outputs(node1).nth(0).unwrap();
        assert!(g.link_ports(node0_input, node1_input).is_err());
        assert!(g.link_ports(node0_output, node1_output).is_err());
        g.link_ports(node0_output, node0_input).unwrap();
        assert!(g.link_ports(node0_output, node1_input).is_err());
        g.unlink_port(node0_output);
        g.remove_node(node1);
        assert!(g.link_ports(node1_output, node0_input).is_err());
    }
}
