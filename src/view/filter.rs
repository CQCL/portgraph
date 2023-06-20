//! Wrappers around portgraphs to filter out nodes and ports.

use crate::{Direction, LinkView, MultiView, NodeIndex, PortIndex, PortView};

use context_iterators::{ContextIterator, FilterCtx, IntoContextIterator, WithCtx};
use delegate::delegate;

/// Node filter used by [`NodeFiltered`].
pub type NodeFilter<Ctx> = fn(NodeIndex, &Ctx) -> bool;

/// A wrapper around a portgraph that filters out nodes.
#[derive(Debug, Clone, PartialEq)]
pub struct NodeFiltered<'a, G, F, Context = ()> {
    graph: &'a G,
    filter: F,
    context: Context,
}

impl<'a, G, F, Ctx> NodeFiltered<'a, G, F, Ctx> {
    /// Create a new node filtered portgraph.
    pub fn new(graph: &'a G, filter: F, context: Ctx) -> Self {
        Self {
            graph,
            filter,
            context,
        }
    }

    /// Get the filter's context.
    pub fn context(&self) -> &Ctx {
        &self.context
    }
}

/// Filter functions used on the items of the [`NodeFiltered`] iterators.
impl<G, Ctx> NodeFiltered<'_, G, NodeFilter<Ctx>, Ctx> {
    /// Node filter used for the iterators
    fn node_filter(node: &NodeIndex, ctx: &NodeFilterCtx<G, Ctx>) -> bool
    where
        G: PortView,
    {
        (ctx.filter)(*node, ctx.context)
    }

    /// Port filter used for the iterators
    fn port_filter(port: &(impl Into<PortIndex> + Copy), ctx: &NodeFilterCtx<G, Ctx>) -> bool
    where
        G: PortView,
    {
        let node = ctx.graph.port_node(*port).unwrap();
        (ctx.filter)(node, ctx.context)
    }

    /// Link filter used for the iterators
    fn link_filter(link: &(G::LinkEndpoint, G::LinkEndpoint), ctx: &NodeFilterCtx<G, Ctx>) -> bool
    where
        G: LinkView,
    {
        let (from, to) = link;
        let from_node = ctx.graph.port_node(*from).unwrap();
        let to_node = ctx.graph.port_node(*to).unwrap();
        (ctx.filter)(from_node, ctx.context) && (ctx.filter)(to_node, ctx.context)
    }
}

/// Context used internally for the [`NodeFiltered`] iterators.
///
/// This is a named struct to make the iterator signatures more readable.
pub struct NodeFilterCtx<'a, G, Ctx> {
    pub(self) graph: &'a G,
    pub(self) filter: NodeFilter<Ctx>,
    pub(self) context: &'a Ctx,
}

impl<'a, G, Ctx> NodeFilterCtx<'a, G, Ctx> {
    /// Create a new context.
    pub(self) fn new(graph: &'a G, filter: NodeFilter<Ctx>, context: &'a Ctx) -> Self {
        Self {
            graph,
            filter,
            context,
        }
    }
}

/// Non-capturing filter function used by [`NodeFiltered`].
type NodeFilterFn<Item, G, Ctx> = fn(&Item, &NodeFilterCtx<G, Ctx>) -> bool;

/// Node-filtered iterator wrapper used by [`NodeFiltered`].
pub type NodeFilteredIter<'a, G, Ctx, I> =
    FilterCtx<WithCtx<I, NodeFilterCtx<'a, G, Ctx>>, NodeFilterFn<<I as Iterator>::Item, G, Ctx>>;

impl<G, Ctx> PortView for NodeFiltered<'_, G, NodeFilter<Ctx>, Ctx>
where
    G: PortView,
{
    type Nodes<'a> = NodeFilteredIter<'a, G, Ctx, <G as PortView>::Nodes<'a>>
    where
        Self: 'a;

    type Ports<'a> = NodeFilteredIter<'a, G, Ctx, <G as PortView>::Ports<'a>>
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
        self.graph.contains_node(node) && (self.filter)(node, &self.context)
    }

    #[inline]
    fn contains_port(&self, port: PortIndex) -> bool {
        if self.graph.contains_port(port) {
            let node = self.graph.port_node(port).unwrap();
            (self.filter)(node, &self.context)
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
            .with_context(NodeFilterCtx::new(self.graph, self.filter, &self.context))
            .filter_with_context(Self::node_filter)
    }

    #[inline]
    fn ports_iter(&self) -> Self::Ports<'_> {
        self.graph
            .ports_iter()
            .with_context(NodeFilterCtx::new(self.graph, self.filter, &self.context))
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

impl<G, Ctx> LinkView for NodeFiltered<'_, G, NodeFilter<Ctx>, Ctx>
where
    G: LinkView,
{
    type LinkEndpoint = G::LinkEndpoint;

    type Neighbours<'a> = NodeFilteredIter<'a, G, Ctx, <G as LinkView>::Neighbours<'a>>
    where
        Self: 'a;

    type NodeConnections<'a> = NodeFilteredIter<'a, G, Ctx, <G as LinkView>::NodeConnections<'a>>
    where
        Self: 'a;

    type NodeLinks<'a> = NodeFilteredIter<'a, G, Ctx, <G as LinkView>::NodeLinks<'a>>
    where
        Self: 'a;

    type PortLinks<'a> = NodeFilteredIter<'a, G, Ctx, <G as LinkView>::PortLinks<'a>>
    where
        Self: 'a;

    fn get_connections(&self, from: NodeIndex, to: NodeIndex) -> Self::NodeConnections<'_> {
        self.graph
            .get_connections(from, to)
            .with_context(NodeFilterCtx::new(self.graph, self.filter, &self.context))
            .filter_with_context(Self::link_filter)
    }

    fn port_links(&self, port: PortIndex) -> Self::PortLinks<'_> {
        self.graph
            .port_links(port)
            .with_context(NodeFilterCtx::new(self.graph, self.filter, &self.context))
            .filter_with_context(Self::link_filter)
    }

    fn links(&self, node: NodeIndex, direction: Direction) -> Self::NodeLinks<'_> {
        self.graph
            .links(node, direction)
            .with_context(NodeFilterCtx::new(self.graph, self.filter, &self.context))
            .filter_with_context(Self::link_filter)
    }

    fn all_links(&self, node: NodeIndex) -> Self::NodeLinks<'_> {
        self.graph
            .all_links(node)
            .with_context(NodeFilterCtx::new(self.graph, self.filter, &self.context))
            .filter_with_context(Self::link_filter)
    }

    fn neighbours(&self, node: NodeIndex, direction: Direction) -> Self::Neighbours<'_> {
        self.graph
            .neighbours(node, direction)
            .with_context(NodeFilterCtx::new(self.graph, self.filter, &self.context))
            .filter_with_context(Self::node_filter)
    }

    fn all_neighbours(&self, node: NodeIndex) -> Self::Neighbours<'_> {
        self.graph
            .all_neighbours(node)
            .with_context(NodeFilterCtx::new(self.graph, self.filter, &self.context))
            .filter_with_context(Self::node_filter)
    }

    fn link_count(&self) -> usize {
        self.nodes_iter()
            .flat_map(|node| self.all_links(node))
            .count()
    }
}

impl<G, Ctx> MultiView for NodeFiltered<'_, G, NodeFilter<Ctx>, Ctx>
where
    G: MultiView,
{
    type NodeSubports<'a> = NodeFilteredIter<'a, G, Ctx, <G as MultiView>::NodeSubports<'a>>
    where
        Self: 'a;

    fn subports(&self, node: NodeIndex, direction: Direction) -> Self::NodeSubports<'_> {
        self.graph
            .subports(node, direction)
            .with_context(NodeFilterCtx::new(self.graph, self.filter, &self.context))
            .filter_with_context(Self::port_filter)
    }

    fn all_subports(&self, node: NodeIndex) -> Self::NodeSubports<'_> {
        self.graph
            .all_subports(node)
            .with_context(NodeFilterCtx::new(self.graph, self.filter, &self.context))
            .filter_with_context(Self::port_filter)
    }

    delegate! {
        to self.graph {
            fn subport_link(&self, subport: Self::LinkEndpoint) -> Option<Self::LinkEndpoint>;
        }
    }
}
