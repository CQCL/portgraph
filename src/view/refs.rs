//! Trait implementations for references
//!
//! Note: The `auto_impl` crate would do all of this for us,
//! but it does not support GATs at the moment.

use crate::{Direction, NodeIndex, PortIndex, PortOffset};

use delegate::delegate;

use super::{LinkView, PortView};

impl<'g, G: PortView> PortView for &'g G {
    type Nodes<'a> = G::Nodes<'a>
    where
        Self: 'a;

    type Ports<'a> = G::Ports<'a>
    where
        Self: 'a;

    type NodePorts<'a> = G::NodePorts<'a>
    where
        Self: 'a;

    type NodePortOffsets<'a> = G::NodePortOffsets<'a>
    where
        Self: 'a;

    delegate! {
        to (*self) {
            fn port_direction(&self, port: impl Into<PortIndex>) -> Option<Direction>;
            fn port_node(&self, port: impl Into<PortIndex>) -> Option<NodeIndex>;
            fn port_offset(&self, port: impl Into<PortIndex>) -> Option<PortOffset>;
            fn port_index(&self, node: NodeIndex, offset: PortOffset) -> Option<PortIndex>;
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

impl<'g, G: LinkView> LinkView for &'g G {
    type LinkEndpoint = G::LinkEndpoint;

    type Neighbours<'a> = G::Neighbours<'a>
    where
        Self: 'a;

    type NodeConnections<'a> = G::NodeConnections<'a>
    where
        Self: 'a;

    type NodeLinks<'a> = G::NodeLinks<'a>
    where
        Self: 'a;

    type PortLinks<'a> = G::PortLinks<'a>
    where
        Self: 'a;

    delegate! {
        to (*self) {
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

// TODO: PortMut, LinkMut, MultiView, MultiMut
