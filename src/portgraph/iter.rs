//! Iterator structures for a portgraph

use std::{
    iter::{Flatten, FusedIterator, Zip},
    num::NonZeroU32,
    ops::Range,
};

use crate::portgraph::{NodeEntry, PortEntry, PortGraph};
use crate::{NodeIndex, PortIndex, PortOffset};

/// Iterator over the ports of a node.
/// See [`PortGraph::inputs`], [`PortGraph::outputs`], and [`PortGraph::all_ports`].
#[derive(Debug, Clone)]
pub struct NodePorts {
    pub(super) index: NonZeroU32,
    pub(super) length: usize,
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
        self.length = self.length.checked_sub(n + 1)?;
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

impl DoubleEndedIterator for NodePorts {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.length = self.length.checked_sub(1)?;
        let port = PortIndex(self.index.saturating_add(self.length as u32));
        Some(port)
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

/// Iterator over the nodes of a graph, created by [`PortGraph::nodes_iter`].
#[derive(Clone)]
pub struct Nodes<'a> {
    pub(super) iter: std::iter::Enumerate<std::slice::Iter<'a, NodeEntry>>,
    pub(super) len: usize,
}

impl<'a> Iterator for Nodes<'a> {
    type Item = NodeIndex;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.find_map(|(index, node_meta)| match node_meta {
            NodeEntry::Free(_) => None,
            NodeEntry::Node(_) => {
                self.len -= 1;
                Some(NodeIndex::new(index))
            }
        })
    }

    #[inline]
    fn count(self) -> usize {
        self.len
    }

    #[inline]
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
            if let NodeEntry::Node(_) = node_meta {
                self.len -= 1;
                return Some(NodeIndex::new(index));
            }
        }

        None
    }
}

impl<'a> FusedIterator for Nodes<'a> {}

/// Iterator over the ports of a graph, created by [`PortGraph::ports_iter`].
#[derive(Clone)]
pub struct Ports<'a> {
    pub(super) iter: std::iter::Enumerate<std::slice::Iter<'a, PortEntry>>,
    pub(super) len: usize,
}

impl<'a> Iterator for Ports<'a> {
    type Item = PortIndex;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        for (index, port_entry) in &mut self.iter {
            if let PortEntry::Port(_) = port_entry {
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

/// Iterator over the port offsets of a node. See [`PortGraph::input_offsets`],
/// [`PortGraph::output_offsets`], and [`PortGraph::all_port_offsets`].
#[derive(Clone)]
pub struct NodePortOffsets {
    pub(super) incoming: Range<u16>,
    // Outgoing port offsets can go up to u16::MAX, hence the u32
    pub(super) outgoing: Range<u32>,
}

impl Iterator for NodePortOffsets {
    type Item = PortOffset;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(i) = self.incoming.next() {
            return Some(PortOffset::new_incoming(i as usize));
        }
        if let Some(i) = self.outgoing.next() {
            return Some(PortOffset::new_outgoing(i as usize));
        }
        None
    }

    fn count(self) -> usize {
        self.len()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl ExactSizeIterator for NodePortOffsets {
    fn len(&self) -> usize {
        self.incoming.len() + self.outgoing.len()
    }
}

impl DoubleEndedIterator for NodePortOffsets {
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(i) = self.outgoing.next_back() {
            return Some(PortOffset::new_outgoing(i as usize));
        }
        if let Some(i) = self.incoming.next_back() {
            return Some(PortOffset::new_incoming(i as usize));
        }
        None
    }
}

impl FusedIterator for NodePortOffsets {}

/// Iterator over the links of a node, created by [`PortGraph::links`]. Returns
/// the port indices linked to each port, or `None` if the corresponding port is
/// not connected.
#[derive(Clone)]
pub struct NodeLinks<'a>(pub(super) std::slice::Iter<'a, Option<PortIndex>>);

impl<'a> Iterator for NodeLinks<'a> {
    type Item = Option<PortIndex>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().copied()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth(n).copied()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a> ExactSizeIterator for NodeLinks<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a> DoubleEndedIterator for NodeLinks<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().copied()
    }
}

impl<'a> FusedIterator for NodeLinks<'a> {}

/// Iterator over the neighbours of a node, created by
/// [`PortGraph::neighbours`]. May return duplicate entries if the graph has
/// multiple links between the same pair of nodes.
#[derive(Clone)]
pub struct Neighbours<'a> {
    graph: &'a PortGraph,
    linked_ports: Flatten<NodeLinks<'a>>,
}

impl<'a> Neighbours<'a> {
    /// Create a new iterator over the neighbours of a node, from an iterator
    /// over the links.
    pub fn from_node_links(graph: &'a PortGraph, links: NodeLinks<'a>) -> Self {
        Self {
            graph,
            linked_ports: links.flatten(),
        }
    }
}

impl<'a> Iterator for Neighbours<'a> {
    type Item = NodeIndex;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.linked_ports
            .next()
            .map(|port| self.graph.port_node(port).unwrap())
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.linked_ports.size_hint()
    }
}

impl<'a> DoubleEndedIterator for Neighbours<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.linked_ports
            .next_back()
            .map(|port| self.graph.port_node(port).unwrap())
    }
}

impl<'a> FusedIterator for Neighbours<'a> {}

/// Iterator over the links connecting two nodes, created by
/// [`PortGraph::get_connections`].
#[derive(Clone)]
pub struct NodeConnections<'a> {
    graph: &'a PortGraph,
    target: NodeIndex,
    port_links: Zip<NodePorts, NodeLinks<'a>>,
}

impl<'a> NodeConnections<'a> {
    /// Create a new iterator over the links connecting two nodes, from an
    /// iterator over the ports and links.
    pub fn new(
        graph: &'a PortGraph,
        target: NodeIndex,
        ports: NodePorts,
        links: NodeLinks<'a>,
    ) -> Self {
        Self {
            graph,
            target,
            port_links: ports.zip(links),
        }
    }

    /// Checks if we can yield an element from the `port_links` iterator.
    ///
    /// Receives `self.graph` and `self.target` as arguments to avoid borrowing issues.
    fn get_next(
        graph: &PortGraph,
        target: NodeIndex,
        next: (PortIndex, Option<PortIndex>),
    ) -> Option<(PortIndex, PortIndex)> {
        let (from, to) = next;
        let to = to?;
        if graph.port_node(to) == Some(target) {
            Some((from, to))
        } else {
            None
        }
    }
}

impl<'a> Iterator for NodeConnections<'a> {
    type Item = (PortIndex, PortIndex);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.port_links
            .find_map(|next| Self::get_next(self.graph, self.target, next))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.port_links.size_hint()
    }
}

impl<'a> DoubleEndedIterator for NodeConnections<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.port_links
            .try_rfold((), |_, next| {
                Self::get_next(self.graph, self.target, next).map_or(Ok(()), Err)
            })
            .err()
    }
}

impl<'a> FusedIterator for NodeConnections<'a> {}
