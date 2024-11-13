//! Trait implementations for references
//!
//! Note: The `auto_impl` crate would do all of this for us,
//! but it does not support GATs at the moment.

use crate::{Direction, NodeIndex, PortIndex, PortOffset};

use delegate::delegate;

use super::{LinkView, PortView};

impl<'g, G: PortView> PortView for &'g G {
    delegate! {
        to (*self) {
            fn port_direction(&self, port: impl Into<PortIndex>) -> Option<Direction>;
            fn port_node(&self, port: impl Into<PortIndex>) -> Option<NodeIndex>;
            fn port_offset(&self, port: impl Into<PortIndex>) -> Option<PortOffset>;
            fn port_index(&self, node: NodeIndex, offset: PortOffset) -> Option<PortIndex>;
            fn ports(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = PortIndex>;
            fn all_ports(&self, node: NodeIndex) -> impl Iterator<Item = PortIndex>;
            fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn num_ports(&self, node: NodeIndex, direction: Direction) -> usize;
            fn port_offsets(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = PortOffset>;
            fn all_port_offsets(&self, node: NodeIndex) -> impl Iterator<Item = PortOffset>;
            fn contains_node(&self, node: NodeIndex) -> bool;
            fn contains_port(&self, port: PortIndex) -> bool;
            fn is_empty(&self) -> bool;
            fn node_count(&self) -> usize;
            fn port_count(&self) -> usize;
            fn nodes_iter(&self) -> impl Iterator<Item = NodeIndex>;
            fn ports_iter(&self) -> impl Iterator<Item = PortIndex>;
            fn node_capacity(&self) -> usize;
            fn port_capacity(&self) -> usize;
            fn node_port_capacity(&self, node: NodeIndex) -> usize;
        }
    }
}

impl<'g, G: LinkView> LinkView for &'g G {
    type LinkEndpoint = G::LinkEndpoint;

    delegate! {
        to (*self) {
            fn get_connections(&self, from: NodeIndex, to: NodeIndex) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)>;
            fn port_links(&self, port: PortIndex) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)>;
            fn links(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)>;
            fn all_links(&self, node: NodeIndex) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)>;
            fn neighbours(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = NodeIndex>;
            fn all_neighbours(&self, node: NodeIndex) -> impl Iterator<Item = NodeIndex>;
            fn link_count(&self) -> usize;
        }
    }
}

// TODO: PortMut, LinkMut, MultiView, MultiMut
