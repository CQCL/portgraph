//! View of a portgraph containing only the children of a node in a [`Hierarchy`].

use super::filter::NodeFiltered;
use crate::{Direction, Hierarchy, LinkView, MultiView, NodeIndex, PortIndex, PortView};

use delegate::delegate;

type RegionContext<'g> = (&'g Hierarchy, NodeIndex);
type RegionCallback<'g> = fn(NodeIndex, &RegionContext<'g>) -> bool;
type RegionInternalGraph<'g, G> = NodeFiltered<'g, G, RegionCallback<'g>, RegionContext<'g>>;

/// View of a portgraph containing only the children of a node in a [`Hierarchy`].
pub struct Region<'g, G> {
    graph: RegionInternalGraph<'g, G>,
    root: NodeIndex,
}

impl<'a, G> Region<'a, G> {
    /// Create a new region view.
    pub fn new(graph: &'a G, hierarchy: &'a Hierarchy, root: NodeIndex) -> Self {
        let region_filter: RegionCallback<'a> = |node, context| {
            let (hierarchy, root) = context;
            hierarchy.parent(node) == Some(*root)
        };
        Self {
            graph: NodeFiltered::new(graph, region_filter, (hierarchy, root)),
            root,
        }
    }

    /// Get the root node of the region.
    pub fn root(&self) -> NodeIndex {
        self.root
    }
}

impl<'g, G> PortView for Region<'g, G>
where
    G: PortView,
{
    type Nodes<'a> = <RegionInternalGraph<'g, G> as PortView>::Nodes<'a>
    where
        Self: 'a;

    type Ports<'a> = <RegionInternalGraph<'g, G> as PortView>::Ports<'a>
    where
        Self: 'a;

    type NodePorts<'a> = <RegionInternalGraph<'g, G> as PortView>::NodePorts<'a>
    where
        Self: 'a;

    type NodePortOffsets<'a> = <RegionInternalGraph<'g, G> as PortView>::NodePortOffsets<'a>
    where
        Self: 'a;

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
            fn contains_node(&self, node: NodeIndex) -> bool;
            fn contains_port(&self, port: PortIndex) -> bool;
            fn is_empty(&self) -> bool;
            fn node_count(&self) -> usize;
            fn port_count(&self) -> usize;
            fn nodes_iter(&self) -> Self::Nodes<'_>;
            fn ports_iter(&self) -> Self::Ports<'_>;
            fn node_capacity(&self) -> usize;
            fn port_capacity(&self) -> usize;
            fn node_port_capacity(&self, node: NodeIndex) -> usize;
        }
    }
}

impl<'g, G> LinkView for Region<'g, G>
where
    G: LinkView,
{
    type LinkEndpoint = G::LinkEndpoint;

    type Neighbours<'a> = <RegionInternalGraph<'g, G> as LinkView>::Neighbours<'a>
    where
        Self: 'a;

    type NodeConnections<'a> = <RegionInternalGraph<'g, G> as LinkView>::NodeConnections<'a>
    where
        Self: 'a;

    type NodeLinks<'a> = <RegionInternalGraph<'g, G> as LinkView>::NodeLinks<'a>
    where
        Self: 'a;

    type PortLinks<'a> = <RegionInternalGraph<'g, G> as LinkView>::PortLinks<'a>
    where
        Self: 'a;

    delegate! {
        to self.graph {
            fn get_connections(&self, from: NodeIndex, to: NodeIndex) -> Self::NodeConnections<'_>;
            fn port_links(&self, port: PortIndex) -> Self::PortLinks<'_>;
            fn links(&self, node: NodeIndex, direction: Direction) -> Self::NodeLinks<'_>;
            fn all_links(&self, node: NodeIndex) -> Self::NodeLinks<'_>;
            fn neighbours(&self, node: NodeIndex, direction: Direction) -> Self::Neighbours<'_>;
            fn all_neighbours(&self, node: NodeIndex) -> Self::Neighbours<'_>;
            fn link_count(&self) -> usize;
        }
    }
}

impl<'g, G> MultiView for Region<'g, G>
where
    G: MultiView,
{
    type NodeSubports<'a> = <RegionInternalGraph<'g, G> as MultiView>::NodeSubports<'a>
    where
        Self: 'a;

    delegate! {
            to self.graph {
        fn subport_link(&self, subport: Self::LinkEndpoint) -> Option<Self::LinkEndpoint>;
        fn subports(&self, node: NodeIndex, direction: Direction) -> Self::NodeSubports<'_>;
        fn all_subports(&self, node: NodeIndex) -> Self::NodeSubports<'_>;
    }}
}
