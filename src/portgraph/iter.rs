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
impl<Node: NodeIndex, Port: PortIndex, Offset: PortOffset> PortGraph<Node, Port, Offset> {
    /// Iterates over all the ports of the `node` in the given `direction`.
    pub(crate) fn _ports(&self, node: Node, direction: Direction) -> NodePorts<Port> {
        match self.node_meta_valid(node) {
            Some(node_meta) => NodePorts {
                indices: node_meta.ports(direction),
                phantom: std::marker::PhantomData,
            },
            None => NodePorts::default(),
        }
    }

    /// Iterates over all the input ports of the `node`.
    ///
    /// Shorthand for [`PortView::ports`].
    #[must_use]
    #[inline]
    pub(crate) fn _inputs(&self, node: Node) -> NodePorts<Port> {
        self._ports(node, Direction::Incoming)
    }

    /// Iterates over all the output ports of the `node`.
    ///
    /// Shorthand for [`PortView::ports`].
    #[must_use]
    #[inline]
    pub(crate) fn _outputs(&self, node: Node) -> NodePorts<Port> {
        self._ports(node, Direction::Outgoing)
    }

    /// Iterates over the input and output ports of the `node` in sequence.
    pub(crate) fn _all_ports(&self, node: Node) -> NodePorts<Port> {
        match self.node_meta_valid(node) {
            Some(node_meta) => NodePorts {
                indices: node_meta.all_ports(),
                phantom: std::marker::PhantomData,
            },
            None => NodePorts::default(),
        }
    }

    /// Iterates over all the port offsets of the `node` in the given `direction`.
    pub(crate) fn _port_offsets(
        &self,
        node: Node,
        direction: Direction,
    ) -> NodePortOffsets<Offset> {
        match direction {
            Direction::Incoming => NodePortOffsets {
                incoming: 0..self.num_inputs(node) as u16,
                outgoing: 0..0,
                phantom: std::marker::PhantomData,
            },
            Direction::Outgoing => NodePortOffsets {
                incoming: 0..0,
                outgoing: 0..self.num_outputs(node) as u32,
                phantom: std::marker::PhantomData,
            },
        }
    }

    /// Iterates over the input and output port offsets of the `node` in sequence.
    #[inline]
    pub(crate) fn _all_port_offsets(&self, node: Node) -> NodePortOffsets<Offset> {
        NodePortOffsets {
            incoming: 0..self.num_inputs(node) as u16,
            outgoing: 0..self.num_outputs(node) as u32,
            phantom: std::marker::PhantomData,
        }
    }

    /// Iterates over the nodes in the port graph.
    #[inline]
    pub(crate) fn _nodes_iter(&self) -> Nodes<Node, Port, Offset> {
        Nodes {
            iter: self.node_meta.iter().enumerate(),
            len: self.node_count,
        }
    }

    /// Iterates over the ports in the port graph.
    #[inline]
    pub(crate) fn _ports_iter(&self) -> Ports<Node, Port> {
        Ports {
            iter: self.port_meta.iter().enumerate(),
            len: self.port_count,
            phantom: std::marker::PhantomData,
        }
    }

    /// Returns an iterator over every pair of matching ports connecting `from`
    /// with `to`.
    #[inline]
    pub(crate) fn _get_connections(
        &self,
        from: Node,
        to: Node,
    ) -> NodeConnections<Node, Port, Offset> {
        NodeConnections::new(self, to, self._links(from, Direction::Outgoing))
    }

    /// Iterates over the connected links of the `node` in the given
    /// `direction`.
    pub(crate) fn _links(&self, node: Node, direction: Direction) -> NodeLinks<Port> {
        let Some(node_meta) = self.node_meta_valid(node) else {
            return NodeLinks::new(self._ports(node, direction), &[], 0..0);
        };
        let indices = node_meta.ports(direction);
        NodeLinks::new(self._ports(node, direction), &self.port_link[indices], 0..0)
    }

    /// Iterates over the connected input and output links of the `node` in sequence.
    pub(crate) fn _all_links(&self, node: Node) -> NodeLinks<Port> {
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
    pub(crate) fn _neighbours(
        &self,
        node: Node,
        direction: Direction,
    ) -> Neighbours<Node, Port, Offset> {
        Neighbours::from_node_links(self, self._links(node, direction))
    }

    /// Iterates over the input and output neighbours of the `node` in sequence.
    #[inline]
    pub(crate) fn _all_neighbours(&self, node: Node) -> Neighbours<Node, Port, Offset> {
        Neighbours::from_node_links(self, self._all_links(node))
    }
}

/// Iterator over the ports of a node.
/// See [`PortGraph::inputs`], [`PortGraph::outputs`], and [`PortGraph::all_ports`].
#[derive(Debug, Clone)]
pub struct NodePorts<Port> {
    pub(super) indices: Range<usize>,
    phantom: std::marker::PhantomData<Port>,
}

impl<Port> Default for NodePorts<Port> {
    fn default() -> Self {
        Self {
            indices: Default::default(),
            phantom: Default::default(),
        }
    }
}

impl<Port: PortIndex> NodePorts<Port> {
    /// Return the leftover ports in the iterator as a range of integer indexes.
    #[inline]
    pub fn as_range(&self) -> Range<usize> {
        self.indices.clone()
    }
}

impl<Port: PortIndex> Iterator for NodePorts<Port> {
    type Item = Port;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.indices.next().map(Port::port_from_usize)
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.indices.nth(n).map(Port::port_from_usize)
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

impl<Port: PortIndex> ExactSizeIterator for NodePorts<Port> {
    fn len(&self) -> usize {
        self.indices.len()
    }
}

impl<Port: PortIndex> DoubleEndedIterator for NodePorts<Port> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.indices.next_back().map(Port::port_from_usize)
    }
}

impl<Port: PortIndex> FusedIterator for NodePorts<Port> {}

/// Iterator over the nodes of a graph, created by [`PortGraph::nodes_iter`].
#[derive(Clone, Debug, Default)]
pub struct Nodes<'a, Node: NodeIndex, Port: PortIndex, Offset: PortOffset> {
    pub(super) iter: std::iter::Enumerate<std::slice::Iter<'a, NodeEntry<Node, Port, Offset>>>,
    pub(super) len: usize,
}

impl<Node: NodeIndex, Port: PortIndex, Offset: PortOffset> Iterator
    for Nodes<'_, Node, Port, Offset>
{
    type Item = Node;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.find_map(|(index, node_meta)| match node_meta {
            NodeEntry::Free(_) => None,
            NodeEntry::Node(_) => {
                self.len -= 1;
                Some(Node::node_from_usize(index))
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

impl<Node: NodeIndex, Port: PortIndex, Offset: PortOffset> ExactSizeIterator
    for Nodes<'_, Node, Port, Offset>
{
    fn len(&self) -> usize {
        self.len
    }
}

impl<Node: NodeIndex, Port: PortIndex, Offset: PortOffset> DoubleEndedIterator
    for Nodes<'_, Node, Port, Offset>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        while let Some((index, node_meta)) = self.iter.next_back() {
            if let NodeEntry::Node(_) = node_meta {
                self.len -= 1;
                return Some(Node::node_from_usize(index));
            }
        }

        None
    }
}

impl<Node: NodeIndex, Port: PortIndex, Offset: PortOffset> FusedIterator
    for Nodes<'_, Node, Port, Offset>
{
}

/// Iterator over the ports of a graph, created by [`PortGraph::ports_iter`].
#[derive(Clone, Debug, Default)]
pub struct Ports<'a, Node, Port> {
    pub(super) iter: std::iter::Enumerate<std::slice::Iter<'a, PortEntry<Node>>>,
    pub(super) len: usize,
    phantom: std::marker::PhantomData<Port>,
}

impl<Node: NodeIndex, Port: PortIndex> Iterator for Ports<'_, Node, Port> {
    type Item = Port;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.find_map(|(index, port_entry)| match port_entry {
            PortEntry::Port(_) => {
                self.len -= 1;
                Some(Port::port_from_usize(index))
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

impl<Node: NodeIndex, Port: PortIndex> ExactSizeIterator for Ports<'_, Node, Port> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<Node: NodeIndex, Port: PortIndex> DoubleEndedIterator for Ports<'_, Node, Port> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some((index, port_entry)) = self.iter.next_back() {
            if let PortEntry::Port(_) = port_entry {
                self.len -= 1;
                return Some(Port::port_from_usize(index));
            }
        }
        None
    }
}

impl<Node: NodeIndex, Port: PortIndex> FusedIterator for Ports<'_, Node, Port> {}

/// Iterator over the port offsets of a node. See [`PortGraph::input_offsets`],
/// [`PortGraph::output_offsets`], and [`PortGraph::all_port_offsets`].
#[derive(Clone, Debug, Default)]
pub struct NodePortOffsets<Offset> {
    pub(super) incoming: Range<u16>,
    // Outgoing port offsets can go up to u16::MAX, hence the u32
    pub(super) outgoing: Range<u32>,
    phantom: std::marker::PhantomData<Offset>,
}

impl<Offset> NodePortOffsets<Offset> {
    /// Return the leftover ports in the iterator as a range of integer indexes.
    #[inline]
    pub fn as_range(&self, dir: Direction) -> Range<usize> {
        match dir {
            Direction::Incoming => self.incoming.start as usize..self.incoming.end as usize,
            Direction::Outgoing => self.outgoing.start as usize..self.outgoing.end as usize,
        }
    }
}

impl<Offset: PortOffset> Iterator for NodePortOffsets<Offset> {
    type Item = Offset;

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

impl<Offset: PortOffset> ExactSizeIterator for NodePortOffsets<Offset> {
    fn len(&self) -> usize {
        self.incoming.len() + self.outgoing.len()
    }
}

impl<Offset: PortOffset> DoubleEndedIterator for NodePortOffsets<Offset> {
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

impl<Offset: PortOffset> FusedIterator for NodePortOffsets<Offset> {}

/// Iterator over the links of a node, created by [`LinkView::links`]. Returns
/// the port indices linked to each port.
///
/// [`LinkView::links`]: crate::LinkView::links
#[derive(Clone, Debug)]
pub struct NodeLinks<'a, Port: PortIndex> {
    links: Zip<NodePorts<Port>, std::slice::Iter<'a, Option<Port>>>,
    /// Ignore links with target ports in the given range.
    /// This is used to filter out duplicated self-links.
    ignore_target_ports: Range<usize>,
}

impl<'a, Port: PortIndex> NodeLinks<'a, Port> {
    /// Returns a new iterator
    pub(super) fn new(
        ports: NodePorts<Port>,
        links: &'a [Option<Port>],
        ignore_target_ports: Range<usize>,
    ) -> Self {
        Self {
            links: ports.zip(links.iter()),
            ignore_target_ports,
        }
    }
}

impl<Port: PortIndex> Iterator for NodeLinks<'_, Port> {
    type Item = (Port, Port);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (port, link) = self.links.next()?;
            let Some(link) = link else {
                continue;
            };
            if self.ignore_target_ports.contains(&link.port_as_usize()) {
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

impl<Port: PortIndex> DoubleEndedIterator for NodeLinks<'_, Port> {
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

impl<Port: PortIndex> FusedIterator for NodeLinks<'_, Port> {}

/// Iterator over the neighbours of a node, created by
/// [`LinkView::neighbours`]. May return duplicate entries if the graph has
/// multiple links between the same pair of nodes.
///
/// [`LinkView::neighbours`]: crate::LinkView::neighbours
#[derive(Clone, Debug)]
pub struct Neighbours<'a, Node: NodeIndex, Port: PortIndex, Offset: PortOffset> {
    graph: &'a PortGraph<Node, Port, Offset>,
    linked_ports: NodeLinks<'a, Port>,
}

impl<'a, Node: NodeIndex, Port: PortIndex, Offset: PortOffset> Neighbours<'a, Node, Port, Offset> {
    /// Create a new iterator over the neighbours of a node, from an iterator
    /// over the links.
    pub fn from_node_links(
        graph: &'a PortGraph<Node, Port, Offset>,
        links: NodeLinks<'a, Port>,
    ) -> Self {
        Self {
            graph,
            linked_ports: links,
        }
    }
}

impl<Node: NodeIndex, Port: PortIndex, Offset: PortOffset> Iterator
    for Neighbours<'_, Node, Port, Offset>
{
    type Item = Node;

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

impl<Node: NodeIndex, Port: PortIndex, Offset: PortOffset> DoubleEndedIterator
    for Neighbours<'_, Node, Port, Offset>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.linked_ports
            .next_back()
            .map(|(_, port)| self.graph.port_node(port).unwrap())
    }
}

impl<Node: NodeIndex, Port: PortIndex, Offset: PortOffset> FusedIterator
    for Neighbours<'_, Node, Port, Offset>
{
}

/// Iterator over the links connecting two nodes, created by
/// [`LinkView::get_connections`].
///
/// [`LinkView::get_connections`]: crate::LinkView::get_connections
#[derive(Clone, Debug)]
pub struct NodeConnections<'a, Node: NodeIndex, Port: PortIndex, Offset: PortOffset> {
    graph: &'a PortGraph<Node, Port, Offset>,
    target: Node,
    port_links: NodeLinks<'a, Port>,
}

impl<'a, Node: NodeIndex, Port: PortIndex, Offset: PortOffset>
    NodeConnections<'a, Node, Port, Offset>
{
    /// Create a new iterator over the links connecting two nodes, from an
    /// iterator over the ports and links.
    pub fn new(
        graph: &'a PortGraph<Node, Port, Offset>,
        target: Node,
        links: NodeLinks<'a, Port>,
    ) -> Self {
        Self {
            graph,
            target,
            port_links: links,
        }
    }
}

impl<Node: NodeIndex, Port: PortIndex, Offset: PortOffset> Iterator
    for NodeConnections<'_, Node, Port, Offset>
{
    type Item = (Port, Port);

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

impl<Node: NodeIndex, Port: PortIndex, Offset: PortOffset> DoubleEndedIterator
    for NodeConnections<'_, Node, Port, Offset>
{
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

impl<Node: NodeIndex, Port: PortIndex, Offset: PortOffset> FusedIterator
    for NodeConnections<'_, Node, Port, Offset>
{
}
