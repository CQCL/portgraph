//! Iterator structures for a portgraph

use std::{
    iter::{FusedIterator, Zip},
    ops::Range,
};

use crate::{
    portgraph::{NodeEntry, PortEntry, PortGraph},
    Direction, PortView,
};
use crate::{NodeIndex, PortIndex, PortOffset};

/// Iterator methods for [`PortGraph`] with concrete return types.
///
/// Used internally by other iterator implementations to avoid the generic RPITIT return types.
impl PortGraph {
    /// Iterates over all the ports of the `node` in the given `direction`.
    pub(crate) fn _ports(&self, node: NodeIndex, direction: Direction) -> NodePorts {
        match self.node_meta_valid(node) {
            Some(node_meta) => NodePorts {
                indices: node_meta.ports(direction),
            },
            None => NodePorts::default(),
        }
    }

    /// Iterates over all the input ports of the `node`.
    ///
    /// Shorthand for [`PortView::ports`].
    #[must_use]
    #[inline]
    pub(crate) fn _inputs(&self, node: NodeIndex) -> NodePorts {
        self._ports(node, Direction::Incoming)
    }

    /// Iterates over all the output ports of the `node`.
    ///
    /// Shorthand for [`PortView::ports`].
    #[must_use]
    #[inline]
    pub(crate) fn _outputs(&self, node: NodeIndex) -> NodePorts {
        self._ports(node, Direction::Outgoing)
    }

    /// Iterates over the input and output ports of the `node` in sequence.
    pub(crate) fn _all_ports(&self, node: NodeIndex) -> NodePorts {
        match self.node_meta_valid(node) {
            Some(node_meta) => NodePorts {
                indices: node_meta.all_ports(),
            },
            None => NodePorts::default(),
        }
    }

    /// Iterates over all the port offsets of the `node` in the given `direction`.
    pub(crate) fn _port_offsets(&self, node: NodeIndex, direction: Direction) -> NodePortOffsets {
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

    /// Iterates over the input and output port offsets of the `node` in sequence.
    #[inline]
    pub(crate) fn _all_port_offsets(&self, node: NodeIndex) -> NodePortOffsets {
        NodePortOffsets {
            incoming: 0..self.num_inputs(node) as u16,
            outgoing: 0..self.num_outputs(node) as u32,
        }
    }

    /// Iterates over the nodes in the port graph.
    #[inline]
    pub(crate) fn _nodes_iter(&self) -> Nodes {
        Nodes {
            iter: self.node_meta.iter().enumerate(),
            len: self.node_count,
        }
    }

    /// Iterates over the ports in the port graph.
    #[inline]
    pub(crate) fn _ports_iter(&self) -> Ports {
        Ports {
            iter: self.port_meta.iter().enumerate(),
            len: self.port_count,
        }
    }

    /// Returns an iterator over every pair of matching ports connecting `from`
    /// with `to`.
    #[inline]
    pub(crate) fn _get_connections(&self, from: NodeIndex, to: NodeIndex) -> NodeConnections {
        NodeConnections::new(self, to, self._links(from, Direction::Outgoing))
    }

    /// Iterates over the connected links of the `node` in the given
    /// `direction`.
    pub(crate) fn _links(&self, node: NodeIndex, direction: Direction) -> NodeLinks {
        let Some(node_meta) = self.node_meta_valid(node) else {
            return NodeLinks::new(self._ports(node, direction), &[], 0..0);
        };
        let indices = node_meta.ports(direction);
        NodeLinks::new(self._ports(node, direction), &self.port_link[indices], 0..0)
    }

    /// Iterates over the connected input and output links of the `node` in sequence.
    pub(crate) fn _all_links(&self, node: NodeIndex) -> NodeLinks {
        let Some(node_meta) = self.node_meta_valid(node) else {
            return NodeLinks::new(self._all_ports(node), &[], 0..0);
        };
        let indices = node_meta.all_ports();
        // Ignore links where the target is one of the node's output ports.
        // This way we only count self-links once.
        NodeLinks::new(
            self._all_ports(node),
            &self.port_link[indices],
            node_meta.outgoing_ports(),
        )
    }

    /// Iterates over neighbour nodes in the given `direction`.
    /// May contain duplicates if the graph has multiple links between nodes.
    #[inline]
    pub(crate) fn _neighbours(&self, node: NodeIndex, direction: Direction) -> Neighbours {
        Neighbours::from_node_links(self, self._links(node, direction))
    }

    /// Iterates over the input and output neighbours of the `node` in sequence.
    #[inline]
    pub(crate) fn _all_neighbours(&self, node: NodeIndex) -> Neighbours {
        Neighbours::from_node_links(self, self._all_links(node))
    }
}

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
#[derive(Clone, Debug, Default)]
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
#[derive(Clone, Debug, Default)]
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

impl<'a> ExactSizeIterator for Ports<'a> {
    fn len(&self) -> usize {
        self.len
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
#[derive(Clone, Debug, Default)]
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

/// Iterator over the links of a node, created by [`LinkView::links`]. Returns
/// the port indices linked to each port.
///
/// [`LinkView::links`]: crate::LinkView::links
#[derive(Clone, Debug)]
pub struct NodeLinks<'a> {
    links: Zip<NodePorts, std::slice::Iter<'a, Option<PortIndex>>>,
    /// Ignore links with target ports in the given range.
    /// This is used to filter out duplicated self-links.
    ignore_target_ports: Range<usize>,
}

impl<'a> NodeLinks<'a> {
    /// Returns a new iterator
    pub(super) fn new(
        ports: NodePorts,
        links: &'a [Option<PortIndex>],
        ignore_target_ports: Range<usize>,
    ) -> Self {
        Self {
            links: ports.zip(links.iter()),
            ignore_target_ports,
        }
    }
}

impl<'a> Iterator for NodeLinks<'a> {
    type Item = (PortIndex, PortIndex);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (port, link) = self.links.next()?;
            let Some(link) = link else {
                continue;
            };
            if self.ignore_target_ports.contains(&link.index()) {
                continue;
            }
            return Some((port, *link));
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.links.size_hint().1)
    }
}

impl<'a> DoubleEndedIterator for NodeLinks<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            let (port, link) = self.links.next_back()?;
            if let Some(link) = link {
                return Some((port, *link));
            }
        }
    }
}

impl<'a> FusedIterator for NodeLinks<'a> {}

/// Iterator over the neighbours of a node, created by
/// [`LinkView::neighbours`]. May return duplicate entries if the graph has
/// multiple links between the same pair of nodes.
///
/// [`LinkView::neighbours`]: crate::LinkView::neighbours
#[derive(Clone, Debug)]
pub struct Neighbours<'a> {
    graph: &'a PortGraph,
    linked_ports: NodeLinks<'a>,
}

impl<'a> Neighbours<'a> {
    /// Create a new iterator over the neighbours of a node, from an iterator
    /// over the links.
    pub fn from_node_links(graph: &'a PortGraph, links: NodeLinks<'a>) -> Self {
        Self {
            graph,
            linked_ports: links,
        }
    }
}

impl<'a> Iterator for Neighbours<'a> {
    type Item = NodeIndex;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.linked_ports
            .next()
            .map(|(_, port)| self.graph.port_node(port).unwrap())
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
            .map(|(_, port)| self.graph.port_node(port).unwrap())
    }
}

impl<'a> FusedIterator for Neighbours<'a> {}

/// Iterator over the links connecting two nodes, created by
/// [`LinkView::get_connections`].
///
/// [`LinkView::get_connections`]: crate::LinkView::get_connections
#[derive(Clone, Debug)]
pub struct NodeConnections<'a> {
    graph: &'a PortGraph,
    target: NodeIndex,
    port_links: NodeLinks<'a>,
}

impl<'a> NodeConnections<'a> {
    /// Create a new iterator over the links connecting two nodes, from an
    /// iterator over the ports and links.
    pub fn new(graph: &'a PortGraph, target: NodeIndex, links: NodeLinks<'a>) -> Self {
        Self {
            graph,
            target,
            port_links: links,
        }
    }
}

impl<'a> Iterator for NodeConnections<'a> {
    type Item = (PortIndex, PortIndex);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (src, tgt) = self.port_links.next()?;
            if self.graph.port_node(tgt) == Some(self.target) {
                return Some((src, tgt));
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.port_links.size_hint()
    }
}

impl<'a> DoubleEndedIterator for NodeConnections<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            let (src, tgt) = self.port_links.next_back()?;
            if self.graph.port_node(tgt) == Some(self.target) {
                return Some((src, tgt));
            }
        }
    }
}

impl<'a> FusedIterator for NodeConnections<'a> {}
