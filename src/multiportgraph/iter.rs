//! Iterators used by the implementation of HugrView for Hugr.

use std::fmt::Debug;
use std::iter::{Enumerate, FusedIterator};
use std::ops::Range;

use super::{MultiPortGraph, SubportIndex};
use crate::portgraph::{self, NodePorts};
use crate::{Direction, LinkView, NodeIndex, PortIndex, PortOffset, PortView};

/// Iterator methods for [`MultiPortGraph`] with concrete return types.
///
/// Used internally by other iterator implementations to avoid the generic RPITIT return types.
impl MultiPortGraph {
    /// Iterates over all the subports of the `node` in the given `direction`.
    #[inline]
    pub(crate) fn _subports(&self, node: NodeIndex, direction: Direction) -> NodeSubports {
        NodeSubports::new(self, self.graph._ports(node, direction))
    }

    /// Iterates over the input and output subports of the `node` in sequence.
    #[inline]
    pub(crate) fn _all_subports(&self, node: NodeIndex) -> NodeSubports {
        NodeSubports::new(self, self.graph._all_ports(node))
    }
}

/// Iterator over the nodes of a graph.
#[derive(Clone)]
pub struct Nodes<'a> {
    // We use portgraph's iterator, but filter out the copy nodes.
    pub(super) multigraph: &'a MultiPortGraph,
    pub(super) iter: portgraph::Nodes<'a>,
    pub(super) len: usize,
}

impl Iterator for Nodes<'_> {
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

impl ExactSizeIterator for Nodes<'_> {
    fn len(&self) -> usize {
        self.len
    }
}

impl DoubleEndedIterator for Nodes<'_> {
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

impl FusedIterator for Nodes<'_> {}

/// Iterator over the ports of a node.
#[derive(Debug, Clone)]
pub struct NodeSubports<'a> {
    multigraph: &'a MultiPortGraph,
    ports: portgraph::NodePorts,
    current_port: Option<PortIndex>,
    current_subports: Range<usize>,
}

impl<'a> NodeSubports<'a> {
    pub(super) fn new(multigraph: &'a MultiPortGraph, ports: portgraph::NodePorts) -> Self {
        Self {
            multigraph,
            ports,
            current_port: None,
            current_subports: 0..0,
        }
    }
}

impl Iterator for NodeSubports<'_> {
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
                    .as_range(dir);
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

impl FusedIterator for NodeSubports<'_> {}

/// Iterator over the ports of a node.
#[derive(Debug, Clone)]
pub struct Neighbours<'a> {
    multigraph: &'a MultiPortGraph,
    subports: NodeSubports<'a>,
    current_copy_node: Option<NodeIndex>,
    /// The node for which the neighbours are being iterated.
    node: NodeIndex,
    /// Whether to ignore self-loops in the input -> output direction.
    /// This is used to avoid counting self-loops twice when iterating both
    /// input and output neighbours.
    ignore_dupped_self_loops: bool,
}

impl<'a> Neighbours<'a> {
    pub(super) fn new(
        multigraph: &'a MultiPortGraph,
        subports: NodeSubports<'a>,
        node: NodeIndex,
        ignore_dupped_self_loops: bool,
    ) -> Self {
        Self {
            multigraph,
            subports,
            current_copy_node: None,
            node,
            ignore_dupped_self_loops,
        }
    }
}

impl Iterator for Neighbours<'_> {
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
                        self.current_copy_node = self.multigraph.get_copy_node(port_index);
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

impl FusedIterator for Neighbours<'_> {}

/// Iterator over the links from a node, created by
/// [`MultiPortGraph::links`].
///
/// In contrast to [`portgraph::NodeLinks`], this iterator
/// only returns linked subports, and includes the source subport.
#[derive(Debug, Clone)]
pub struct NodeLinks<'a> {
    multigraph: &'a MultiPortGraph,
    ports: NodePorts,
    current_links: Option<PortLinks<'a>>,
    /// Ignore links to the given target ports.
    /// This is used to avoid counting self-loops twice.
    ignore_target_ports: Range<usize>,
}

impl<'a> NodeLinks<'a> {
    pub(super) fn new(
        multigraph: &'a MultiPortGraph,
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

impl Iterator for NodeLinks<'_> {
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

impl FusedIterator for NodeLinks<'_> {}

/// Iterator over the links between two nodes, created by
/// [`MultiPortGraph::get_connections`].
#[derive(Debug, Clone)]
pub struct NodeConnections<'a, NL: 'a> {
    multigraph: &'a MultiPortGraph,
    target: NodeIndex,
    links: NL,
}

impl<'a, NL: Iterator<Item = (SubportIndex, SubportIndex)> + 'a> NodeConnections<'a, NL> {
    pub(super) fn new(multigraph: &'a MultiPortGraph, target: NodeIndex, links: NL) -> Self {
        Self {
            multigraph,
            target,
            links,
        }
    }
}

impl<'a, NL: Iterator<Item = (SubportIndex, SubportIndex)> + 'a> Iterator
    for NodeConnections<'a, NL>
{
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

impl<'a, NL: Iterator<Item = (SubportIndex, SubportIndex)> + 'a> FusedIterator
    for NodeConnections<'a, NL>
{
}

/// Iterator over the links of a port
#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub enum PortLinks<'a> {
    /// The port is not a multiport. The iterator returns exactly one link.
    SinglePort {
        multigraph: &'a MultiPortGraph,
        port: PortIndex,
        empty: bool,
    },
    /// The port is a multiport. The iterator may return any number of links.
    Multiport {
        multigraph: &'a MultiPortGraph,
        port: PortIndex,
        subports: Enumerate<portgraph::NodePorts>,
    },
}

impl<'a> PortLinks<'a> {
    pub(super) fn new(multigraph: &'a MultiPortGraph, port: PortIndex) -> Self {
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
fn port_links_single(
    multigraph: &MultiPortGraph,
    port: PortIndex,
) -> Option<(SubportIndex, SubportIndex)> {
    let link = multigraph.graph.port_link(port)?;
    let link = multigraph.get_subport_from_index(link)?;
    Some((SubportIndex::new_unique(port), link))
}

/// Try to get the next link of a multiport for a `PortLinks` iterator.
#[inline(always)]
fn port_links_multiport(
    multigraph: &MultiPortGraph,
    port: PortIndex,
    subport_offset: usize,
    copy_port_index: PortIndex,
) -> Option<(SubportIndex, SubportIndex)> {
    let link = multigraph.graph.port_link(copy_port_index)?;
    let link = multigraph.get_subport_from_index(link)?;
    Some((SubportIndex::new_multi(port, subport_offset), link))
}

impl Iterator for PortLinks<'_> {
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

impl DoubleEndedIterator for PortLinks<'_> {
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

impl FusedIterator for PortLinks<'_> {}

/// Iterator over all the ports of the multiport graph.
#[derive(Clone)]
pub struct Ports<'a> {
    /// The multiport graph.
    multigraph: &'a MultiPortGraph,
    /// The wrapped ports iterator.
    ///
    /// We filter out the copy nodes from here.
    ports: portgraph::Ports<'a>,
}

impl<'a> Ports<'a> {
    pub(super) fn new(multigraph: &'a MultiPortGraph, ports: portgraph::Ports<'a>) -> Self {
        Self { multigraph, ports }
    }
}

impl Iterator for Ports<'_> {
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

impl DoubleEndedIterator for Ports<'_> {
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

impl FusedIterator for Ports<'_> {}
