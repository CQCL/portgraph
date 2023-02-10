use std::{
    iter::FusedIterator,
    mem::{replace, take},
    num::NonZeroU32,
};

use crate::graph::Direction;
use thiserror::Error;

#[derive(Debug, Clone)]
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

            assert!(port_list.index() + size < self.port_link.len());

            for i in port_list.index()..port_list.index() + size {
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
        if size - 1 >= self.port_free.len() {
            self.port_free.resize(size, None);
        }

        let ports_free = &mut self.port_free[size - 1];

        self.port_meta[ports.index()] = PortMeta::new_free();
        self.port_link[ports.index()] = replace(ports_free, Some(ports));
    }

    pub fn link(&mut self, port_from: PortIndex, port_to: PortIndex) -> Result<(), LinkError> {
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

        self.port_link[port_from.index()] = Some(port_to);
        self.port_link[port_to.index()] = Some(port_from);

        Ok(())
    }

    pub fn unlink(&mut self, port: PortIndex) -> Option<PortIndex> {
        self.port_meta_valid(port)?;
        let linked = take(&mut self.port_link[port.index()])?;
        self.port_link[linked.index()] = None;
        Some(linked)
    }

    #[inline]
    pub fn port_direction(&self, port: PortIndex) -> Option<Direction> {
        Some(self.port_meta_valid(port)?.direction())
    }

    #[inline]
    pub fn port_node(&self, port: PortIndex) -> Option<NodeIndex> {
        Some(self.port_meta_valid(port)?.node())
    }

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

    #[inline]
    pub fn port_link(&self, port: PortIndex) -> Option<PortIndex> {
        self.port_meta_valid(port)?;
        self.port_link[port.index()]
    }

    pub fn node_ports(&self, node: NodeIndex, direction: Direction) -> NodePorts {
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

    pub fn node_links(&self, node: NodeIndex, direction: Direction) -> &[Option<PortIndex>] {
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
    pub fn is_empty(&self) -> bool {
        self.node_count == 0 && self.port_count == 0
    }

    #[inline]
    pub fn node_count(&self) -> usize {
        self.node_count
    }

    #[inline]
    pub fn port_count(&self) -> usize {
        self.port_count
    }

    #[inline]
    pub fn nodes(&self) -> Nodes<'_> {
        Nodes {
            iter: self.node_meta.iter().enumerate(),
            len: self.node_count,
        }
    }

    #[inline]
    pub fn ports(&self) -> Ports<'_> {
        Ports {
            iter: self.port_meta.iter().enumerate(),
            len: self.port_count,
        }
    }

    pub fn clear(&mut self) {
        self.node_meta.clear();
        self.port_link.clear();
        self.port_meta.clear();
        self.node_free = None;
        self.port_free.clear();
        self.node_count = 0;
        self.port_count = 0;
    }

    // TODO: Reserve functions

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
        Self(node.index() as u32 | direction)
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeIndex(NonZeroU32);

impl NodeIndex {
    #[inline]
    pub fn new(index: usize) -> Self {
        //assert!(index < u32::MAX as usize);
        Self(NonZeroU32::new(index as u32 + 1).unwrap())
    }

    #[inline]
    pub fn index(self) -> usize {
        u32::from(self.0) as usize - 1
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PortIndex(NonZeroU32);

impl PortIndex {
    #[inline]
    pub fn new(index: usize) -> Self {
        assert!(index < u32::MAX as usize);
        Self(NonZeroU32::new(index as u32 + 1).unwrap())
    }

    #[inline]
    pub fn index(self) -> usize {
        u32::from(self.0) as usize - 1
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
}

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

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        for (index, node_meta) in &mut self.iter {
            if !node_meta.is_free() {
                self.len -= 1;
                return Some(NodeIndex::new(index));
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
