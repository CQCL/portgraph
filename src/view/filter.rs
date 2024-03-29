//! Wrappers around portgraphs to filter out nodes and ports.

use crate::{Direction, LinkView, MultiView, NodeIndex, PortIndex, PortView};

use context_iterators::{ContextIterator, FilterWithCtx, IntoContextIterator, MapWithCtx};
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

    pub(super) fn graph(&self) -> G {
        self.graph.clone()
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
    fn node_filter(node: &NodeIndex, ctx: &FilteredGraphCtx<G, Ctx>) -> bool
    where
        G: PortView,
    {
        (ctx.node_filter)(*node, ctx.context)
    }

    /// Port filter used for the iterators
    ///
    /// A port exists iff its node exists (don't use `link_filter`!)
    fn port_filter(&port: &(impl Into<PortIndex> + Copy), ctx: &FilteredGraphCtx<G, Ctx>) -> bool
    where
        G: PortView,
    {
        let node = ctx.graph.port_node(port).unwrap();
        FilteredGraph::node_filter(&node, ctx)
    }

    /// Link filter used for the iterators
    ///
    /// A link exists if both its ports exist and satisfy `link_filter`.
    fn link_filter(
        link: &(G::LinkEndpoint, G::LinkEndpoint),
        ctx: &FilteredGraphCtx<G, Ctx>,
    ) -> bool
    where
        G: LinkView,
    {
        let &(from, to) = link;
        FilteredGraph::port_filter(&from, ctx)
            && FilteredGraph::port_filter(&to, ctx)
            && (ctx.link_filter)(from.into(), ctx.context)
            && (ctx.link_filter)(to.into(), ctx.context)
    }

    /// The full context used for the iterators
    fn as_context(&self) -> FilteredGraphCtx<'_, G, Ctx>
    where
        G: PortView,
    {
        FilteredGraphCtx::new(
            self.graph.clone(),
            self.node_filter,
            self.link_filter,
            &self.context,
        )
    }
}

/// Context used internally for the [`FilteredGraph`] iterators.
///
/// This is a named struct to make the iterator signatures more readable.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct FilteredGraphCtx<'a, G, Ctx> {
    pub(self) graph: G,
    pub(self) node_filter: NodeFilter<Ctx>,
    pub(self) link_filter: LinkFilter<Ctx>,
    pub(self) context: &'a Ctx,
}

impl<'a, G, Ctx> FilteredGraphCtx<'a, G, Ctx> {
    /// Create a new context.
    pub(self) fn new(
        graph: G,
        node_filter: NodeFilter<Ctx>,
        link_filter: LinkFilter<Ctx>,
        context: &'a Ctx,
    ) -> Self {
        Self {
            graph,
            node_filter,
            link_filter,
            context,
        }
    }
}

/// Filtered iterator wrapper used by [`FilteredGraph`].
pub type FilteredGraphIter<'a, G, Ctx, I> = FilterWithCtx<I, FilteredGraphCtx<'a, G, Ctx>>;
/// Filtered + mapped iterator wrapper used by [`FilteredGraph`].
pub type MapFilteredGraphIter<'a, G, Ctx, I, O> = MapWithCtx<I, FilteredGraphCtx<'a, G, Ctx>, O>;

impl<G, Ctx> PortView for FilteredGraph<G, NodeFilter<Ctx>, LinkFilter<Ctx>, Ctx>
where
    G: PortView + Clone,
{
    type Nodes<'a> = FilteredGraphIter<'a, G, Ctx, <G as PortView>::Nodes<'a>>
    where
        Self: 'a;

    type Ports<'a> = FilteredGraphIter<'a, G, Ctx, <G as PortView>::Ports<'a>>
    where
        Self: 'a;

    type NodePorts<'a> = G::NodePorts<'a>
    where
        Self: 'a;

    type NodePortOffsets<'a> = G::NodePortOffsets<'a>
    where
        Self: 'a;

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
    fn nodes_iter(&self) -> Self::Nodes<'_> {
        self.graph
            .nodes_iter()
            .with_context(self.as_context())
            .filter_with_context(Self::node_filter)
    }

    #[inline]
    fn ports_iter(&self) -> Self::Ports<'_> {
        self.graph
            .ports_iter()
            .with_context(self.as_context())
            .filter_with_context(Self::port_filter)
    }

    delegate! {
        to self.graph {
            fn port_direction(&self, port: impl Into<PortIndex>) -> Option<Direction>;
            fn port_node(&self, port: impl Into<PortIndex>) -> Option<NodeIndex>;
            fn port_offset(&self, port: impl Into<PortIndex>) -> Option<crate::PortOffset>;
            fn port_index(&self, node: NodeIndex, offset: crate::PortOffset) -> Option<PortIndex>;
            fn ports(&self, node: NodeIndex, direction: Direction) -> Self::NodePorts<'_>;
            fn all_ports(&self, node: NodeIndex) -> Self::NodePorts<'_>;
            fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn num_ports(&self, node: NodeIndex, direction: Direction) -> usize;
            fn port_offsets(&self, node: NodeIndex, direction: Direction) -> Self::NodePortOffsets<'_>;
            fn all_port_offsets(&self, node: NodeIndex) -> Self::NodePortOffsets<'_>;
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

    type Neighbours<'a> = MapFilteredGraphIter<'a, G, Ctx, Self::NodeLinks<'a>, NodeIndex>
    where
        Self: 'a;

    type NodeConnections<'a> = FilteredGraphIter<'a, G, Ctx, <G as LinkView>::NodeConnections<'a>>
    where
        Self: 'a;

    type NodeLinks<'a> = FilteredGraphIter<'a, G, Ctx, <G as LinkView>::NodeLinks<'a>>
    where
        Self: 'a;

    type PortLinks<'a> = FilteredGraphIter<'a, G, Ctx, <G as LinkView>::PortLinks<'a>>
    where
        Self: 'a;

    fn get_connections(&self, from: NodeIndex, to: NodeIndex) -> Self::NodeConnections<'_> {
        self.graph
            .get_connections(from, to)
            .with_context(self.as_context())
            .filter_with_context(Self::link_filter)
    }

    fn port_links(&self, port: PortIndex) -> Self::PortLinks<'_> {
        self.graph
            .port_links(port)
            .with_context(self.as_context())
            .filter_with_context(Self::link_filter)
    }

    fn links(&self, node: NodeIndex, direction: Direction) -> Self::NodeLinks<'_> {
        self.graph
            .links(node, direction)
            .with_context(self.as_context())
            .filter_with_context(Self::link_filter)
    }

    fn all_links(&self, node: NodeIndex) -> Self::NodeLinks<'_> {
        self.graph
            .all_links(node)
            .with_context(self.as_context())
            .filter_with_context(Self::link_filter)
    }

    fn neighbours(&self, node: NodeIndex, direction: Direction) -> Self::Neighbours<'_> {
        self.links(node, direction)
            .with_context(self.as_context())
            .map_with_context(|(_, p), ctx| ctx.graph.port_node(p).unwrap())
    }

    fn all_neighbours(&self, node: NodeIndex) -> Self::Neighbours<'_> {
        self.all_links(node)
            .with_context(self.as_context())
            .map_with_context(|(_, p), ctx| ctx.graph.port_node(p).unwrap())
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
    type NodeSubports<'a> = FilteredGraphIter<'a, G, Ctx, <G as MultiView>::NodeSubports<'a>>
    where
        Self: 'a;

    fn subports(&self, node: NodeIndex, direction: Direction) -> Self::NodeSubports<'_> {
        self.graph
            .subports(node, direction)
            .with_context(self.as_context())
            .filter_with_context(Self::port_filter)
    }

    fn all_subports(&self, node: NodeIndex) -> Self::NodeSubports<'_> {
        self.graph
            .all_subports(node)
            .with_context(self.as_context())
            .filter_with_context(Self::port_filter)
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
