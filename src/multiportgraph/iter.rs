//! Iterators used by the implementation of HugrView for Hugr.

use std::fmt::Debug;
use std::iter::{Enumerate, FusedIterator};
use std::ops::Range;

use super::{MultiPortGraph, SubportIndex};
use crate::index::{MaybeNodeIndex, Unsigned};
use crate::portgraph::{self, NodePorts};
use crate::{Direction, LinkView, NodeIndex, PortIndex, PortOffset, PortView};

/// Iterator methods for [`MultiPortGraph`] with concrete return types.
///
/// Used internally by other iterator implementations to avoid the generic RPITIT return types.
impl<PO: Unsigned> MultiPortGraph<u32, u32, PO> {
    #[inline]
    /// Returns an iterator over every pair of matching ports connecting `from`
    /// with `to`.
    pub(crate) fn _get_connections(&self, from: NodeIndex, to: NodeIndex) -> NodeConnections<PO> {
        NodeConnections::new(self, to, self._output_links(from))
    }

    /// Returns the port that the given `port` is linked to.
    #[inline]
    pub(crate) fn _port_links(&self, port: PortIndex) -> PortLinks<PO> {
        PortLinks::new(self, port)
    }

    /// Iterates over the connected links of the `node` in the given
    /// `direction`.
    #[inline]
    pub(crate) fn _links(&self, node: NodeIndex, direction: Direction) -> NodeLinks<PO> {
        NodeLinks::new(self, self.graph._ports(node, direction), 0..0)
    }

    /// Iterates over the connected input and output links of the `node` in sequence.
    #[inline]
    pub(crate) fn _all_links(&self, node: NodeIndex) -> NodeLinks<PO> {
        let output_ports = self.graph.node_outgoing_ports(node);
        NodeLinks::new(self, self.graph._all_ports(node), output_ports)
    }

    /// Iterates over the connected output links of the `node`. Shorthand for
    /// [`LinkView::links`].
    #[must_use]
    #[inline]
    pub(crate) fn _output_links(&self, node: NodeIndex) -> NodeLinks<PO> {
        self._links(node, Direction::Outgoing)
    }

    /// Iterates over neighbour nodes in the given `direction`.
    /// May contain duplicates if the graph has multiple links between nodes.
    #[inline]
    pub(crate) fn _neighbours(&self, node: NodeIndex, direction: Direction) -> Neighbours<PO> {
        Neighbours::new(self, self._subports(node, direction), node, false)
    }

    /// Iterates over the input and output neighbours of the `node` in sequence.
    #[inline]
    pub(crate) fn _all_neighbours(&self, node: NodeIndex) -> Neighbours<PO> {
        Neighbours::new(self, self._all_subports(node), node, true)
    }

    /// Iterates over all the subports of the `node` in the given `direction`.
    #[inline]
    pub(crate) fn _subports(&self, node: NodeIndex, direction: Direction) -> NodeSubports<PO> {
        NodeSubports::new(self, self.graph._ports(node, direction))
    }

    /// Iterates over the input and output subports of the `node` in sequence.
    #[inline]
    pub(crate) fn _all_subports(&self, node: NodeIndex) -> NodeSubports<PO> {
        NodeSubports::new(self, self.graph._all_ports(node))
    }
}

/// Iterator over the nodes of a graph.
#[derive(Clone)]
pub struct Nodes<'a, PO: Unsigned> {
    // We use portgraph's iterator, but filter out the copy nodes.
    pub(super) multigraph: &'a MultiPortGraph<u32, u32, PO>,
    pub(super) iter: portgraph::Nodes<'a>,
    pub(super) len: usize,
}

impl<PO: Unsigned> Iterator for Nodes<'_, PO> {
    type Item = NodeIndex;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let next = self
            .iter
            .find(|node| !self.multigraph.is_copy_node(*node))?;
        self.len -= 1;
        Some(next)
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

impl<PO: Unsigned> ExactSizeIterator for Nodes<'_, PO> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<PO: Unsigned> DoubleEndedIterator for Nodes<'_, PO> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            let node = self.iter.next_back()?;
            if !self.multigraph.is_copy_node(node) {
                self.len -= 1;
                return Some(node);
            }
        }
    }
}

impl<PO: Unsigned> FusedIterator for Nodes<'_, PO> {}

/// Iterator over the ports of a node.
#[derive(Debug, Clone)]
pub struct NodeSubports<'a, PO: Unsigned> {
    multigraph: &'a MultiPortGraph<u32, u32, PO>,
    ports: portgraph::NodePorts,
    current_port: Option<PortIndex>,
    current_subports: Range<usize>,
}

impl<'a, PO: Unsigned> NodeSubports<'a, PO> {
    pub(super) fn new(
        multigraph: &'a MultiPortGraph<u32, u32, PO>,
        ports: portgraph::NodePorts,
    ) -> Self {
        Self {
            multigraph,
            ports,
            current_port: None,
            current_subports: 0..0,
        }
    }
}

impl<PO: Unsigned> Iterator for NodeSubports<'_, PO> {
    type Item = SubportIndex;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(offset) = self.current_subports.next() {
                // We are in the middle of iterating over the subports of a port.
                let current_port = self
                    .current_port
                    .expect("NodeSubports set an invalid current_port value.");
                return Some(SubportIndex::new_multi(current_port, offset));
            }

            // Proceed to the next port.
            let port = self.ports.next()?;
            self.current_port = Some(port);
            if self.multigraph.is_multiport(port) {
                let dir = self.multigraph.graph.port_direction(port).unwrap();
                let copy_node = self
                    .multigraph
                    .get_copy_node(port)
                    .expect("A port was marked as multiport, but no copy node was found.");
                self.current_subports = self
                    .multigraph
                    .graph
                    ._port_offsets(copy_node, dir)
                    .as_range(dir)
                    .clone();
            } else {
                // The port is not a multiport, return the single subport.
                return Some(SubportIndex::new_unique(port));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.ports.len() + self.current_subports.len(), None)
    }
}

impl<PO: Unsigned> FusedIterator for NodeSubports<'_, PO> {}

/// Iterator over the ports of a node.
#[derive(Debug, Clone)]
pub struct Neighbours<'a, PO: Unsigned> {
    multigraph: &'a MultiPortGraph<u32, u32, PO>,
    subports: NodeSubports<'a, PO>,
    current_copy_node: MaybeNodeIndex<u32>,
    /// The node for which the neighbours are being iterated.
    node: NodeIndex,
    /// Whether to ignore self-loops in the input -> output direction.
    /// This is used to avoid counting self-loops twice when iterating both
    /// input and output neighbours.
    ignore_dupped_self_loops: bool,
}

impl<'a, PO: Unsigned> Neighbours<'a, PO> {
    pub(super) fn new(
        multigraph: &'a MultiPortGraph<u32, u32, PO>,
        subports: NodeSubports<'a, PO>,
        node: NodeIndex,
        ignore_dupped_self_loops: bool,
    ) -> Self {
        Self {
            multigraph,
            subports,
            current_copy_node: None.into(),
            node,
            ignore_dupped_self_loops,
        }
    }
}

impl<PO: Unsigned> Iterator for Neighbours<'_, PO> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let link = self.subports.find_map(|subport| {
                let port_index = subport.port();
                if !self.multigraph.is_multiport(port_index) {
                    self.multigraph.graph.port_link(port_index)
                } else {
                    // There is a copy node
                    if subport.offset() == 0 {
                        self.current_copy_node = self.multigraph.get_copy_node(port_index).into();
                    }
                    let copy_node = self
                        .current_copy_node
                        .expect("Copy node not connected to a multiport.");
                    let dir = self.multigraph.graph.port_direction(port_index).unwrap();
                    let offset = PortOffset::new(dir, subport.offset());
                    let subport_index =
                        self.multigraph.graph.port_index(copy_node, offset).unwrap();
                    self.multigraph.graph.port_link(subport_index)
                }
            })?;
            let link_subport = self.multigraph.get_subport_from_index(link).unwrap();
            let node = self
                .multigraph
                .graph
                .port_node(link_subport.port())
                .unwrap();
            // Ignore self-loops in the input -> output direction.
            if self.ignore_dupped_self_loops
                && node == self.node
                && self.multigraph.port_direction(link_subport.port()).unwrap()
                    == Direction::Outgoing
            {
                continue;
            }
            return Some(node);
        }
    }
}

impl<PO: Unsigned> FusedIterator for Neighbours<'_, PO> {}

/// Iterator over the links from a node, created by
/// [`MultiPortGraph::links`].
///
/// In contrast to [`portgraph::NodeLinks`], this iterator
/// only returns linked subports, and includes the source subport.
#[derive(Debug, Clone)]
pub struct NodeLinks<'a, PO: Unsigned> {
    multigraph: &'a MultiPortGraph<u32, u32, PO>,
    ports: NodePorts,
    current_links: Option<PortLinks<'a, PO>>,
    /// Ignore links to the given target ports.
    /// This is used to avoid counting self-loops twice.
    ignore_target_ports: Range<usize>,
}

impl<'a, PO: Unsigned> NodeLinks<'a, PO> {
    pub(super) fn new(
        multigraph: &'a MultiPortGraph<u32, u32, PO>,
        ports: NodePorts,
        ignore_target_ports: Range<usize>,
    ) -> Self {
        Self {
            multigraph,
            ports,
            current_links: None,
            ignore_target_ports,
        }
    }
}

impl<PO: Unsigned> Iterator for NodeLinks<'_, PO> {
    /// A link from one of the node's subports to another subport.
    type Item = (SubportIndex, SubportIndex);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let Some(links) = &mut self.current_links else {
                let port = self.ports.next()?;
                self.current_links = Some(PortLinks::new(self.multigraph, port));
                continue;
            };
            let Some((from, to)) = links.next() else {
                self.current_links = None;
                continue;
            };
            // Ignore self-loops in the input -> output direction.
            if self.ignore_target_ports.contains(&to.port().index()) {
                continue;
            }
            return Some((from, to));
        }
    }
}

impl<PO: Unsigned> FusedIterator for NodeLinks<'_, PO> {}

/// Iterator over the links between two nodes, created by
/// [`MultiPortGraph::get_connections`].
#[derive(Debug, Clone)]
pub struct NodeConnections<'a, PO: Unsigned> {
    multigraph: &'a MultiPortGraph<u32, u32, PO>,
    target: NodeIndex,
    links: NodeLinks<'a, PO>,
}

impl<'a, PO: Unsigned> NodeConnections<'a, PO> {
    pub(super) fn new(
        multigraph: &'a MultiPortGraph<u32, u32, PO>,
        target: NodeIndex,
        links: NodeLinks<'a, PO>,
    ) -> Self {
        Self {
            multigraph,
            target,
            links,
        }
    }
}

impl<PO: Unsigned> Iterator for NodeConnections<'_, PO> {
    /// A link from one of the node's subports to another subport.
    type Item = (SubportIndex, SubportIndex);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (source, target) = self.links.next()?;
            let target_node = self.multigraph.graph.port_node(target.port())?;
            if target_node == self.target {
                return Some((source, target));
            }
        }
    }
}

impl<PO: Unsigned> FusedIterator for NodeConnections<'_, PO> {}

/// Iterator over the links of a port
#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub enum PortLinks<'a, PO: Unsigned> {
    /// The port is not a multiport. The iterator returns exactly one link.
    SinglePort {
        multigraph: &'a MultiPortGraph<u32, u32, PO>,
        port: PortIndex,
        empty: bool,
    },
    /// The port is a multiport. The iterator may return any number of links.
    Multiport {
        multigraph: &'a MultiPortGraph<u32, u32, PO>,
        port: PortIndex,
        subports: Enumerate<portgraph::NodePorts>,
    },
}

impl<'a, PO: Unsigned> PortLinks<'a, PO> {
    pub(super) fn new(multigraph: &'a MultiPortGraph<u32, u32, PO>, port: PortIndex) -> Self {
        if multigraph.is_multiport(port) {
            let copy_node = multigraph.get_copy_node(port).unwrap();
            let dir = multigraph.graph.port_direction(port).unwrap();
            let subports = multigraph.graph._ports(copy_node, dir).enumerate();
            Self::Multiport {
                multigraph,
                port,
                subports,
            }
        } else {
            Self::SinglePort {
                multigraph,
                port,
                empty: false,
            }
        }
    }
}

/// Returns the link of a single port for a `PortLinks` iterator.
#[inline(always)]
fn port_links_single<PO: Unsigned>(
    multigraph: &MultiPortGraph<u32, u32, PO>,
    port: PortIndex,
) -> Option<(SubportIndex, SubportIndex)> {
    let link = multigraph.graph.port_link(port)?;
    let link = multigraph.get_subport_from_index(link)?;
    Some((SubportIndex::new_unique(port), link))
}

/// Try to get the next link of a multiport for a `PortLinks` iterator.
#[inline(always)]
fn port_links_multiport<PO: Unsigned>(
    multigraph: &MultiPortGraph<u32, u32, PO>,
    port: PortIndex,
    subport_offset: usize,
    copy_port_index: PortIndex,
) -> Option<(SubportIndex, SubportIndex)> {
    let link = multigraph.graph.port_link(copy_port_index)?;
    let link = multigraph.get_subport_from_index(link)?;
    Some((SubportIndex::new_multi(port, subport_offset), link))
}

impl<PO: Unsigned> Iterator for PortLinks<'_, PO> {
    type Item = (SubportIndex, SubportIndex);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            PortLinks::SinglePort {
                multigraph,
                port,
                empty,
            } if !*empty => {
                *empty = true;
                port_links_single(multigraph, *port)
            }
            PortLinks::SinglePort { .. } => None,
            PortLinks::Multiport {
                multigraph,
                port,
                subports,
                ..
            } => subports
                .find_map(|(offset, index)| port_links_multiport(multigraph, *port, offset, index)),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            PortLinks::SinglePort { empty, .. } => {
                if *empty {
                    (0, Some(0))
                } else {
                    (1, Some(1))
                }
            }
            PortLinks::Multiport { subports, .. } => (0, Some(subports.len())),
        }
    }
}

impl<PO: Unsigned> DoubleEndedIterator for PortLinks<'_, PO> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            PortLinks::SinglePort {
                multigraph,
                port,
                empty,
            } if !*empty => {
                *empty = true;
                port_links_single(multigraph, *port)
            }
            PortLinks::SinglePort { .. } => None,
            PortLinks::Multiport {
                multigraph,
                port,
                subports,
                ..
            } => loop {
                let (offset, index) = subports.next_back()?;
                if let Some(res) = port_links_multiport(multigraph, *port, offset, index) {
                    return Some(res);
                }
            },
        }
    }
}

impl<PO: Unsigned> FusedIterator for PortLinks<'_, PO> {}

/// Iterator over all the ports of the multiport graph.
#[derive(Clone)]
pub struct Ports<'a, PO: Unsigned> {
    /// The multiport graph.
    multigraph: &'a MultiPortGraph<u32, u32, PO>,
    /// The wrapped ports iterator.
    ///
    /// We filter out the copy nodes from here.
    ports: portgraph::Ports<'a>,
}

impl<'a, PO: Unsigned> Ports<'a, PO> {
    pub(super) fn new(
        multigraph: &'a MultiPortGraph<u32, u32, PO>,
        ports: portgraph::Ports<'a>,
    ) -> Self {
        Self { multigraph, ports }
    }
}

impl<PO: Unsigned> Iterator for Ports<'_, PO> {
    type Item = PortIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.ports.find(|&port| {
            let node = self.multigraph.port_node(port).unwrap();
            !self.multigraph.is_copy_node(node)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.ports.size_hint().1)
    }
}

impl<PO: Unsigned> DoubleEndedIterator for Ports<'_, PO> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            let port = self.ports.next_back()?;
            let node = self.multigraph.port_node(port).unwrap();
            if !self.multigraph.is_copy_node(node) {
                return Some(port);
            }
        }
    }
}

impl<PO: Unsigned> FusedIterator for Ports<'_, PO> {}
