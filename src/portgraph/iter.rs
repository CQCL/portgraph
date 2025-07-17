//! Iterator structures for a portgraph

use std::{
    iter::{FusedIterator, Zip},
    marker::PhantomData,
    ops::Range,
};

use crate::{
    index::Unsigned,
    portgraph::{NodeEntry, PortEntry, PortGraph},
    Direction, PortView,
};
use crate::{NodeIndex, PortIndex, PortOffset};

/// Iterator methods for [`PortGraph`] with concrete return types.
///
/// Used internally by other iterator implementations to avoid the generic RPITIT return types.
impl<PO: Unsigned> PortGraph<u32, u32, PO> {
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
    pub(crate) fn _port_offsets(
        &self,
        node: NodeIndex,
        direction: Direction,
    ) -> NodePortOffsets<PO> {
        match direction {
            Direction::Incoming => NodePortOffsets {
                incoming: 0..self.num_inputs(node),
                outgoing: 0..0,
                _marker: PhantomData,
            },
            Direction::Outgoing => NodePortOffsets {
                incoming: 0..0,
                outgoing: 0..self.num_outputs(node),
                _marker: PhantomData,
            },
        }
    }

    /// Iterates over the input and output port offsets of the `node` in sequence.
    #[inline]
    pub(crate) fn _all_port_offsets(&self, node: NodeIndex) -> NodePortOffsets<PO> {
        NodePortOffsets {
            incoming: 0..self.num_inputs(node),
            outgoing: 0..self.num_outputs(node),
            _marker: PhantomData,
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
    pub(crate) fn _get_connections(&self, from: NodeIndex, to: NodeIndex) -> NodeConnections<PO> {
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
    pub(crate) fn _neighbours(&self, node: NodeIndex, direction: Direction) -> Neighbours<PO> {
        Neighbours::from_node_links(self, self._links(node, direction))
    }

    /// Iterates over the input and output neighbours of the `node` in sequence.
    #[inline]
    pub(crate) fn _all_neighbours(&self, node: NodeIndex) -> Neighbours<PO> {
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

impl Iterator for Nodes<'_> {
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

impl ExactSizeIterator for Nodes<'_> {
    fn len(&self) -> usize {
        self.len
    }
}

impl DoubleEndedIterator for Nodes<'_> {
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

impl FusedIterator for Nodes<'_> {}

/// Iterator over the ports of a graph, created by [`PortGraph::ports_iter`].
#[derive(Clone, Debug, Default)]
pub struct Ports<'a> {
    pub(super) iter: std::iter::Enumerate<std::slice::Iter<'a, PortEntry>>,
    pub(super) len: usize,
}

impl Iterator for Ports<'_> {
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

impl ExactSizeIterator for Ports<'_> {
    fn len(&self) -> usize {
        self.len
    }
}

impl DoubleEndedIterator for Ports<'_> {
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

impl FusedIterator for Ports<'_> {}

/// Iterator over the port offsets of a node. See [`PortGraph::input_offsets`],
/// [`PortGraph::output_offsets`], and [`PortGraph::all_port_offsets`].
#[derive(Clone, Debug, Default)]
pub struct NodePortOffsets<PO> {
    pub(super) incoming: Range<usize>,
    // Outgoing port offsets can go up to u16::MAX, hence the u32
    pub(super) outgoing: Range<usize>,
    /// Marker type of the iterator item type.
    _marker: PhantomData<PO>,
}

impl<PO> NodePortOffsets<PO> {
    /// Return the leftover ports in the iterator as a range of integer indexes.
    #[inline]
    pub fn as_range(&self, dir: Direction) -> &Range<usize> {
        match dir {
            Direction::Incoming => &self.incoming,
            Direction::Outgoing => &self.outgoing,
        }
    }
}

impl<PO: Unsigned> Iterator for NodePortOffsets<PO> {
    type Item = PortOffset<PO>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(i) = self.incoming.next() {
            return Some(PortOffset::new_incoming(i));
        }
        if let Some(i) = self.outgoing.next() {
            return Some(PortOffset::new_outgoing(i));
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

impl<PO: Unsigned> ExactSizeIterator for NodePortOffsets<PO> {
    fn len(&self) -> usize {
        self.incoming.len() + self.outgoing.len()
    }
}

impl<PO: Unsigned> DoubleEndedIterator for NodePortOffsets<PO> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(i) = self.outgoing.next_back() {
            return Some(PortOffset::new_outgoing(i));
        }
        if let Some(i) = self.incoming.next_back() {
            return Some(PortOffset::new_incoming(i));
        }
        None
    }
}

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

impl Iterator for NodeLinks<'_> {
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

impl DoubleEndedIterator for NodeLinks<'_> {
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

impl FusedIterator for NodeLinks<'_> {}

/// Iterator over the neighbours of a node, created by
/// [`LinkView::neighbours`]. May return duplicate entries if the graph has
/// multiple links between the same pair of nodes.
///
/// [`LinkView::neighbours`]: crate::LinkView::neighbours
#[derive(Clone, Debug)]
pub struct Neighbours<'a, PO: Unsigned> {
    graph: &'a PortGraph<u32, u32, PO>,
    linked_ports: NodeLinks<'a>,
}

impl<'a, PO: Unsigned> Neighbours<'a, PO> {
    /// Create a new iterator over the neighbours of a node, from an iterator
    /// over the links.
    pub fn from_node_links(graph: &'a PortGraph<u32, u32, PO>, links: NodeLinks<'a>) -> Self {
        Self {
            graph,
            linked_ports: links,
        }
    }
}

impl<PO: Unsigned> Iterator for Neighbours<'_, PO> {
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

impl<PO: Unsigned> DoubleEndedIterator for Neighbours<'_, PO> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.linked_ports
            .next_back()
            .map(|(_, port)| self.graph.port_node(port).unwrap())
    }
}

impl<PO: Unsigned> FusedIterator for Neighbours<'_, PO> {}

/// Iterator over the links connecting two nodes, created by
/// [`LinkView::get_connections`].
///
/// [`LinkView::get_connections`]: crate::LinkView::get_connections
#[derive(Clone, Debug)]
pub struct NodeConnections<'a, PO: Unsigned> {
    graph: &'a PortGraph<u32, u32, PO>,
    target: NodeIndex,
    port_links: NodeLinks<'a>,
}

impl<'a, PO: Unsigned> NodeConnections<'a, PO> {
    /// Create a new iterator over the links connecting two nodes, from an
    /// iterator over the ports and links.
    pub fn new(
        graph: &'a PortGraph<u32, u32, PO>,
        target: NodeIndex,
        links: NodeLinks<'a>,
    ) -> Self {
        Self {
            graph,
            target,
            port_links: links,
        }
    }
}

impl<PO: Unsigned> Iterator for NodeConnections<'_, PO> {
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

impl<PO: Unsigned> DoubleEndedIterator for NodeConnections<'_, PO> {
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

impl<PO: Unsigned> FusedIterator for NodeConnections<'_, PO> {}
