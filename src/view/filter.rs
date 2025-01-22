//! Wrappers around portgraphs to filter out nodes and ports.

use crate::{Direction, LinkView, MultiView, NodeIndex, PortIndex, PortOffset, PortView};

use delegate::delegate;

/// Node filter used by [`FilteredGraph`].
pub type NodeFilter<Ctx> = fn(NodeIndex, &Ctx) -> bool;
/// Link filter used by [`FilteredGraph`].
///
/// Ports that don't match this predicate will appear disconnected.
pub type LinkFilter<Ctx> = fn(PortIndex, &Ctx) -> bool;

/// A wrapper around a [`PortView`] that filters out nodes and links.
///
/// Both nodes and links can be filtered by providing the filter functions
/// `node_filter` and `link_filter`.
///
/// As ports always occupy a contiguous interval of indices, they cannot be
/// filtered out directly. Instead, when `link_filter` filters out a port it
/// appears as disconnected, effectively remove the link between ports. A link
/// is removed whenever either of its ports is filtered out.
///
/// For the special case of filtering out nodes only, the type alias
/// [`NodeFiltered`] is provided, along with [`NodeFiltered::new_node_filtered`].
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct FilteredGraph<G, FN, FP, Context = ()> {
    graph: G,
    node_filter: FN,
    link_filter: FP,
    context: Context,
}

/// A wrapper around a portgraph that filters out nodes.
pub type NodeFiltered<G, FN, Context = ()> = FilteredGraph<G, FN, LinkFilter<Context>, Context>;

impl<G, FN, FP, Ctx> FilteredGraph<G, FN, FP, Ctx>
where
    G: Clone,
{
    /// Create a new node filtered portgraph.
    pub fn new(graph: G, node_filter: FN, link_filter: FP, context: Ctx) -> Self {
        Self {
            graph,
            node_filter,
            link_filter,
            context,
        }
    }

    /// Get the filter's context.
    pub fn context(&self) -> &Ctx {
        &self.context
    }
}

impl<G, F, Ctx> NodeFiltered<G, F, Ctx>
where
    G: Clone,
{
    /// Create a new node filtered portgraph.
    pub fn new_node_filtered(graph: G, node_filter: F, context: Ctx) -> Self {
        Self::new(graph, node_filter, |_, _| true, context)
    }
}

/// Filter functions used on the items of the [`FilteredGraph`] iterators.
impl<G, Ctx> FilteredGraph<G, NodeFilter<Ctx>, LinkFilter<Ctx>, Ctx>
where
    G: Clone,
{
    /// Node filter used for the iterators
    fn node_filter(&self, node: &NodeIndex) -> bool
    where
        G: PortView,
    {
        (self.node_filter)(*node, &self.context)
    }

    /// Port filter used for the iterators
    ///
    /// A port exists iff its node exists (don't use `link_filter`!)
    fn port_filter(&self, &port: &(impl Into<PortIndex> + Copy)) -> bool
    where
        G: PortView,
    {
        let node = self.graph.port_node(port).unwrap();
        self.node_filter(&node)
    }

    /// Link filter used for the iterators
    ///
    /// A link exists if both its ports exist and satisfy `link_filter`.
    fn link_filter(&self, link: &(G::LinkEndpoint, G::LinkEndpoint)) -> bool
    where
        G: LinkView,
    {
        let &(from, to) = link;
        self.port_filter(&from)
            && self.port_filter(&to)
            && (self.link_filter)(from.into(), &self.context)
            && (self.link_filter)(to.into(), &self.context)
    }
}

impl<G, Ctx> PortView for FilteredGraph<G, NodeFilter<Ctx>, LinkFilter<Ctx>, Ctx>
where
    G: PortView + Clone,
{
    #[inline]
    fn contains_node(&'_ self, node: NodeIndex) -> bool {
        self.graph.contains_node(node) && (self.node_filter)(node, &self.context)
    }

    #[inline]
    fn contains_port(&self, port: PortIndex) -> bool {
        if self.graph.contains_port(port) {
            let node = self.graph.port_node(port).unwrap();
            self.contains_node(node)
        } else {
            false
        }
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.node_count() == 0
    }

    #[inline]
    fn node_count(&self) -> usize {
        self.nodes_iter().count()
    }

    #[inline]
    fn port_count(&self) -> usize {
        self.ports_iter().count()
    }

    #[inline]
    fn nodes_iter(&self) -> impl Iterator<Item = NodeIndex> + Clone {
        self.graph.nodes_iter().filter(|n| self.node_filter(n))
    }

    #[inline]
    fn ports_iter(&self) -> impl Iterator<Item = PortIndex> + Clone {
        self.graph.ports_iter().filter(|p| self.port_filter(p))
    }

    delegate! {
        to self.graph {
            fn port_direction(&self, port: impl Into<PortIndex>) -> Option<Direction>;
            fn port_node(&self, port: impl Into<PortIndex>) -> Option<NodeIndex>;
            fn port_offset(&self, port: impl Into<PortIndex>) -> Option<crate::PortOffset>;
            fn port_index(&self, node: NodeIndex, offset: crate::PortOffset) -> Option<PortIndex>;
            fn ports(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = PortIndex> + Clone;
            fn all_ports(&self, node: NodeIndex) -> impl Iterator<Item = PortIndex> + Clone;
            fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn num_ports(&self, node: NodeIndex, direction: Direction) -> usize;
            fn port_offsets(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = PortOffset> + Clone;
            fn all_port_offsets(&self, node: NodeIndex) -> impl Iterator<Item = PortOffset> + Clone;
            fn node_capacity(&self) -> usize;
            fn port_capacity(&self) -> usize;
            fn node_port_capacity(&self, node: NodeIndex) -> usize;
        }
    }
}

impl<G, Ctx> LinkView for FilteredGraph<G, NodeFilter<Ctx>, LinkFilter<Ctx>, Ctx>
where
    G: LinkView + Clone,
{
    type LinkEndpoint = G::LinkEndpoint;

    fn endpoint_port(&self, end: Self::LinkEndpoint) -> PortIndex {
        self.graph.endpoint_port(end)
    }

    fn get_connections(
        &self,
        from: NodeIndex,
        to: NodeIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        self.graph
            .get_connections(from, to)
            .filter(|l| self.link_filter(l))
    }

    fn port_links(
        &self,
        port: PortIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        self.graph.port_links(port).filter(|l| self.link_filter(l))
    }

    fn links(
        &self,
        node: NodeIndex,
        direction: Direction,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        self.graph
            .links(node, direction)
            .filter(|l| self.link_filter(l))
    }

    fn all_links(
        &self,
        node: NodeIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        self.graph.all_links(node).filter(|l| self.link_filter(l))
    }

    fn neighbours(
        &self,
        node: NodeIndex,
        direction: Direction,
    ) -> impl Iterator<Item = NodeIndex> + Clone {
        self.links(node, direction)
            .map(|(_, p)| self.graph.port_node(p).unwrap())
    }

    fn all_neighbours(&self, node: NodeIndex) -> impl Iterator<Item = NodeIndex> + Clone {
        self.all_links(node)
            .map(|(_, p)| self.graph.port_node(p).unwrap())
    }

    fn link_count(&self) -> usize {
        self.nodes_iter()
            .flat_map(|node| self.all_links(node))
            .count()
    }
}

impl<G, Ctx> MultiView for FilteredGraph<G, NodeFilter<Ctx>, LinkFilter<Ctx>, Ctx>
where
    G: MultiView + Clone,
{
    fn subports(
        &self,
        node: NodeIndex,
        direction: Direction,
    ) -> impl Iterator<Item = Self::LinkEndpoint> + Clone {
        self.graph
            .subports(node, direction)
            .filter(|p| self.port_filter(p))
    }

    fn all_subports(&self, node: NodeIndex) -> impl Iterator<Item = Self::LinkEndpoint> + Clone {
        self.graph
            .all_subports(node)
            .filter(|p| self.port_filter(p))
    }

    fn subport_link(&self, subport: Self::LinkEndpoint) -> Option<Self::LinkEndpoint> {
        if !(self.link_filter)(subport.into(), &self.context) {
            return None;
        }
        let to = self.graph.subport_link(subport)?;
        if !(self.link_filter)(to.into(), &self.context) {
            return None;
        }
        Some(to)
    }
}
