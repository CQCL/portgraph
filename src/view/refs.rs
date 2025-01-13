//! Trait implementations for references
//!
//! Note: The `auto_impl` crate would do all of this for us,
//! but it does not support GATs at the moment.

use crate::{Direction, NodeIndex, PortIndex, PortOffset};

use delegate::delegate;

use super::{LinkView, MultiView, PortView};

impl<G: PortView> PortView for &G {
    delegate! {
        to (*self) {
            fn port_direction(&self, port: impl Into<PortIndex>) -> Option<Direction>;
            fn port_node(&self, port: impl Into<PortIndex>) -> Option<NodeIndex>;
            fn port_offset(&self, port: impl Into<PortIndex>) -> Option<PortOffset>;
            fn port_index(&self, node: NodeIndex, offset: PortOffset) -> Option<PortIndex>;
            fn ports(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = PortIndex> + Clone;
            fn all_ports(&self, node: NodeIndex) -> impl Iterator<Item = PortIndex> + Clone;
            fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn num_ports(&self, node: NodeIndex, direction: Direction) -> usize;
            fn port_offsets(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = PortOffset> + Clone;
            fn all_port_offsets(&self, node: NodeIndex) -> impl Iterator<Item = PortOffset> + Clone;
            fn contains_node(&self, node: NodeIndex) -> bool;
            fn contains_port(&self, port: PortIndex) -> bool;
            fn is_empty(&self) -> bool;
            fn node_count(&self) -> usize;
            fn port_count(&self) -> usize;
            fn nodes_iter(&self) -> impl Iterator<Item = NodeIndex> + Clone;
            fn ports_iter(&self) -> impl Iterator<Item = PortIndex> + Clone;
            fn node_capacity(&self) -> usize;
            fn port_capacity(&self) -> usize;
            fn node_port_capacity(&self, node: NodeIndex) -> usize;
        }
    }
}

impl<G: LinkView> LinkView for &G {
    type LinkEndpoint = G::LinkEndpoint;

    delegate! {
        to (*self) {
            fn get_connections(&self, from: NodeIndex, to: NodeIndex) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone;
            fn port_links(&self, port: PortIndex) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone;
            fn links(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone;
            fn all_links(&self, node: NodeIndex) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone;
            fn neighbours(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = NodeIndex> + Clone;
            fn all_neighbours(&self, node: NodeIndex) -> impl Iterator<Item = NodeIndex> + Clone;
            fn link_count(&self) -> usize;
        }
    }
}

impl<G: MultiView> MultiView for &G {
    delegate! {
        to (*self) {
            fn subports(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = Self::LinkEndpoint> + Clone;
            fn all_subports(&self, node: NodeIndex) -> impl Iterator<Item = Self::LinkEndpoint> + Clone;
            fn subport_link(&self, subport: Self::LinkEndpoint) -> Option<Self::LinkEndpoint>;
        }
    }
}

// TODO: PortMut, LinkMut, MultiMut
