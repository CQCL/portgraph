//! Trait implementations for references
//!
//! Note: The `auto_impl` crate would do all of this for us,
//! but it does not support GATs at the moment.

use crate::{Direction, NodeIndex, PortIndex, PortOffset};

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

    fn port_direction(&self, port: impl Into<PortIndex>) -> Option<Direction> {
        self.port_direction(port)
    }

    fn port_node(&self, port: impl Into<PortIndex>) -> Option<NodeIndex> {
        self.port_node(port)
    }

    fn port_offset(&self, port: impl Into<PortIndex>) -> Option<PortOffset> {
        self.port_offset(port)
    }

    fn port_index(&self, node: NodeIndex, offset: PortOffset) -> Option<PortIndex> {
        self.port_index(node, offset)
    }

    fn ports(&self, node: NodeIndex, direction: Direction) -> Self::NodePorts<'_> {
        self.ports(node, direction)
    }

    fn all_ports(&self, node: NodeIndex) -> Self::NodePorts<'_> {
        self.all_ports(node)
    }

    fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.input(node, offset)
    }

    fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex> {
        self.output(node, offset)
    }

    fn num_ports(&self, node: NodeIndex, direction: Direction) -> usize {
        self.num_ports(node, direction)
    }

    fn port_offsets(&self, node: NodeIndex, direction: Direction) -> Self::NodePortOffsets<'_> {
        self.port_offsets(node, direction)
    }

    fn all_port_offsets(&self, node: NodeIndex) -> Self::NodePortOffsets<'_> {
        self.all_port_offsets(node)
    }

    fn contains_node(&self, node: NodeIndex) -> bool {
        self.contains_node(node)
    }

    fn contains_port(&self, port: PortIndex) -> bool {
        self.contains_port(port)
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn node_count(&self) -> usize {
        self.node_count()
    }

    fn port_count(&self) -> usize {
        self.port_count()
    }

    fn nodes_iter(&self) -> Self::Nodes<'_> {
        self.nodes_iter()
    }

    fn ports_iter(&self) -> Self::Ports<'_> {
        self.ports_iter()
    }

    fn node_capacity(&self) -> usize {
        self.node_capacity()
    }

    fn port_capacity(&self) -> usize {
        self.port_capacity()
    }

    fn node_port_capacity(&self, node: NodeIndex) -> usize {
        self.node_port_capacity(node)
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

    fn get_connections(&self, from: NodeIndex, to: NodeIndex) -> Self::NodeConnections<'_> {
        self.get_connections(from, to)
    }

    fn port_links(&self, port: PortIndex) -> Self::PortLinks<'_> {
        self.port_links(port)
    }

    fn links(&self, node: NodeIndex, direction: Direction) -> Self::NodeLinks<'_> {
        self.links(node, direction)
    }

    fn all_links(&self, node: NodeIndex) -> Self::NodeLinks<'_> {
        self.all_links(node)
    }

    fn neighbours(&self, node: NodeIndex, direction: Direction) -> Self::Neighbours<'_> {
        self.neighbours(node, direction)
    }

    fn all_neighbours(&self, node: NodeIndex) -> Self::Neighbours<'_> {
        self.all_neighbours(node)
    }

    fn link_count(&self) -> usize {
        self.link_count()
    }
}

// TODO: PortMut, LinkMut, MultiView, MultiMut
