//! Iterator structures for a portgraph

use std::{
    iter::{Flatten, FusedIterator, Zip},
    ops::Range,
};

use crate::{
    portgraph::{NodeEntry, PortEntry, PortGraph},
    Direction,
};
use crate::{NodeIndex, PortIndex, PortOffset};

/// Iterator over the ports of a node.
/// See [`PortGraph::inputs`], [`PortGraph::outputs`], and [`PortGraph::all_ports`].
#[derive(Debug, Clone, Default)]
pub struct NodePorts {
    pub(super) indices: Range<usize>,
}

impl NodePorts {
    /// Return the leftover ports in the iterator as a range of integer indexes.
    #[inline]
    pub fn as_range(&self) -> Range<usize> {
        self.indices.clone()
    }
}

impl Iterator for NodePorts {
    type Item = PortIndex;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.indices.next().map(PortIndex::new)
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.indices.nth(n).map(PortIndex::new)
    }

    #[inline]
    fn count(self) -> usize {
        self.indices.count()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.indices.size_hint()
    }
}

impl ExactSizeIterator for NodePorts {
    fn len(&self) -> usize {
        self.indices.len()
    }
}

impl DoubleEndedIterator for NodePorts {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.indices.next_back().map(PortIndex::new)
    }
}

impl FusedIterator for NodePorts {}

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
        self.iter.find_map(|(index, port_entry)| match port_entry {
            PortEntry::Port(_) => {
                self.len -= 1;
                Some(PortIndex::new(index))
            }
            _ => None,
        })
    }

    fn count(self) -> usize {
        self.len
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a> DoubleEndedIterator for Ports<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some((index, port_entry)) = self.iter.next_back() {
            if let PortEntry::Port(_) = port_entry {
                self.len -= 1;
                return Some(PortIndex::new(index));
            }
        }
        None
    }
}

impl<'a> FusedIterator for Ports<'a> {}

/// Iterator over the port offsets of a node. See [`PortGraph::input_offsets`],
/// [`PortGraph::output_offsets`], and [`PortGraph::all_port_offsets`].
#[derive(Clone)]
pub struct NodePortOffsets {
    pub(super) incoming: Range<u16>,
    // Outgoing port offsets can go up to u16::MAX, hence the u32
    pub(super) outgoing: Range<u32>,
}

impl NodePortOffsets {
    /// Return the leftover ports in the iterator as a range of integer indexes.
    #[inline]
    pub fn as_range(&self, dir: Direction) -> Range<usize> {
        match dir {
            Direction::Incoming => self.incoming.start as usize..self.incoming.end as usize,
            Direction::Outgoing => self.outgoing.start as usize..self.outgoing.end as usize,
        }
    }
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
        while let Some(next) = self.port_links.next_back() {
            if let Some(next) = Self::get_next(self.graph, self.target, next) {
                return Some(next);
            }
        }
        None
    }
}

impl<'a> FusedIterator for NodeConnections<'a> {}
