//! View of a portgraph containing only the children of a node in a [`Hierarchy`].

use super::{LinkView, MultiView, PortView};
use crate::{Direction, Hierarchy, NodeIndex, PortIndex, PortOffset};

use delegate::delegate;
use itertools::Either;

/// View of a portgraph containing only a root node and its direct children in a [`Hierarchy`].
///
/// For a view of all descendants, see [`crate::view::Region`].
#[derive(Debug, Clone, PartialEq)]
pub struct FlatRegion<'g, G> {
    /// The base graph
    graph: G,
    /// The root node of the region
    region_root: NodeIndex,
    /// The graph's hierarchy
    hierarchy: &'g Hierarchy,
}

impl<'a, G> FlatRegion<'a, G>
where
    G: Clone,
{
    /// Create a new region view including only a root node and its direct
    /// children in a [`Hierarchy`].
    pub fn new(graph: G, hierarchy: &'a Hierarchy, root: NodeIndex) -> Self {
        Self {
            graph,
            region_root: root,
            hierarchy,
        }
    }

    /// Get the root node of the region.
    pub fn region_root(&self) -> NodeIndex {
        self.region_root
    }
}

impl<'g, G> FlatRegion<'g, G>
where
    G: LinkView + Clone,
{
    /// Utility function to filter out links that are not in the region.
    #[inline(always)]
    fn contains_link(&self, (from, to): (G::LinkEndpoint, G::LinkEndpoint)) -> bool {
        self.contains_endpoint(from) && self.contains_endpoint(to)
    }

    /// Utility function to filter out link endpoints that are not in the region.
    #[inline(always)]
    fn contains_endpoint(&self, e: G::LinkEndpoint) -> bool {
        self.contains_port(e.into())
    }
}

impl<'g, G> PortView for FlatRegion<'g, G>
where
    G: PortView + Clone,
{
    #[inline(always)]
    fn contains_node(&'_ self, node: NodeIndex) -> bool {
        node == self.region_root || self.hierarchy.parent(node) == Some(self.region_root)
    }

    #[inline(always)]
    fn contains_port(&self, port: PortIndex) -> bool {
        let Some(node) = self.graph.port_node(port) else {
            return false;
        };
        self.contains_node(node)
    }

    #[inline]
    fn is_empty(&self) -> bool {
        // The region root is always present
        false
    }

    #[inline]
    fn node_count(&self) -> usize {
        self.hierarchy.child_count(self.region_root) + 1
    }

    #[inline]
    fn port_count(&self) -> usize {
        self.ports_iter().count()
    }

    #[inline]
    fn nodes_iter(&self) -> impl Iterator<Item = NodeIndex> + Clone {
        std::iter::once(self.region_root).chain(self.hierarchy.children(self.region_root))
    }

    #[inline]
    fn ports_iter(&self) -> impl Iterator<Item = PortIndex> + Clone {
        self.nodes_iter().flat_map(|n| self.graph.all_ports(n))
    }

    #[inline]
    fn node_capacity(&self) -> usize {
        self.graph.node_capacity() - self.graph.node_count() + self.node_count()
    }

    #[inline]
    fn port_capacity(&self) -> usize {
        self.graph.port_capacity() - self.graph.port_count() + self.port_count()
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
            fn node_port_capacity(&self, node: NodeIndex) -> usize;
        }
    }
}

impl<'g, G> LinkView for FlatRegion<'g, G>
where
    G: LinkView + Clone,
{
    type LinkEndpoint = G::LinkEndpoint;

    fn get_connections(
        &self,
        from: NodeIndex,
        to: NodeIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        if self.contains_node(from) && self.contains_node(to) {
            Either::Left(self.graph.get_connections(from, to))
        } else {
            Either::Right(std::iter::empty())
        }
    }

    fn port_links(
        &self,
        port: PortIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        self.graph
            .port_links(port)
            .filter(|&lnk| self.contains_link(lnk))
    }

    fn links(
        &self,
        node: NodeIndex,
        direction: Direction,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        self.graph
            .links(node, direction)
            .filter(|&lnk| self.contains_link(lnk))
    }

    fn all_links(
        &self,
        node: NodeIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        self.graph
            .all_links(node)
            .filter(|&lnk| self.contains_link(lnk))
    }

    fn neighbours(
        &self,
        node: NodeIndex,
        direction: Direction,
    ) -> impl Iterator<Item = NodeIndex> + Clone {
        self.graph
            .neighbours(node, direction)
            .filter(|&n| self.contains_node(n))
    }

    fn all_neighbours(&self, node: NodeIndex) -> impl Iterator<Item = NodeIndex> + Clone {
        self.graph
            .all_neighbours(node)
            .filter(|&n| self.contains_node(n))
    }

    fn link_count(&self) -> usize {
        self.nodes_iter()
            .flat_map(|node| self.links(node, Direction::Outgoing))
            .count()
    }
}

impl<'g, G> MultiView for FlatRegion<'g, G>
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
            .filter(|&p| self.contains_endpoint(p))
    }

    fn all_subports(&self, node: NodeIndex) -> impl Iterator<Item = Self::LinkEndpoint> + Clone {
        self.graph
            .all_subports(node)
            .filter(|&p| self.contains_endpoint(p))
    }

    fn subport_link(&self, subport: Self::LinkEndpoint) -> Option<Self::LinkEndpoint> {
        self.graph
            .subport_link(subport)
            .filter(|&p| self.contains_endpoint(p))
    }
}

#[cfg(test)]
mod test {
    use std::error::Error;

    use itertools::Itertools;

    use crate::multiportgraph::SubportIndex;
    use crate::{Hierarchy, LinkMut, MultiPortGraph, PortGraph, PortMut};

    use super::*;

    #[test]
    fn single_node_region() {
        let mut graph = PortGraph::new();
        let root = graph.add_node(0, 0);

        let hierarchy = Hierarchy::new();

        let region = FlatRegion::new(&graph, &hierarchy, root);
        assert_eq!(region.node_count(), 1);
        assert_eq!(region.port_count(), 0);
    }

    #[test]
    fn simple_flat_region() -> Result<(), Box<dyn Error>> {
        let mut graph = PortGraph::new();
        let other = graph.add_node(42, 0);
        let root = graph.add_node(1, 0);
        let a = graph.add_node(1, 2);
        let b = graph.add_node(0, 0);
        let c = graph.add_node(0, 0);
        graph.link_nodes(a, 0, other, 0)?;
        graph.link_nodes(a, 1, root, 0)?;

        let mut hierarchy = Hierarchy::new();
        hierarchy.push_child(root, other)?;
        hierarchy.push_child(a, root)?;
        hierarchy.push_child(b, root)?;
        hierarchy.push_child(c, b)?;

        let region = FlatRegion::new(&graph, &hierarchy, root);

        assert!(!region.is_empty());
        assert_eq!(region.region_root(), root);
        assert_eq!(region.node_count(), 3);
        assert_eq!(region.port_count(), 4);
        assert_eq!(region.node_capacity(), graph.node_capacity() - 2);
        assert_eq!(region.port_capacity(), graph.port_capacity() - 42);
        assert_eq!(region.node_port_capacity(a), graph.node_port_capacity(a));
        assert_eq!(
            region.port_offsets(a, Direction::Outgoing).collect_vec(),
            graph.port_offsets(a, Direction::Outgoing).collect_vec()
        );

        assert!(!region.contains_node(other));
        assert!(!region.contains_node(c));
        assert!(region.contains_node(root));
        assert!(!region.contains_port(graph.input(other, 10).unwrap()));
        assert!(region.contains_port(graph.output(a, 0).unwrap()));

        assert_eq!(region.inputs(a).count(), 1);
        assert_eq!(region.outputs(a).count(), 2);
        assert_eq!(region.num_ports(a, Direction::Incoming), 1);
        assert_eq!(region.num_ports(a, Direction::Outgoing), 2);
        assert_eq!(region.all_ports(a).count(), 3);
        assert_eq!(region.all_port_offsets(a).count(), 3);

        let inputs = region
            .inputs(a)
            .enumerate()
            .map(|(i, port)| (i, port, Direction::Incoming));
        let outputs = region
            .outputs(a)
            .enumerate()
            .map(|(i, port)| (i, port, Direction::Outgoing));
        for (i, port, dir) in inputs.chain(outputs) {
            let offset = PortOffset::new(dir, i);
            assert_eq!(region.port_direction(port), Some(dir));
            assert_eq!(region.port_offset(port), Some(offset));
            assert_eq!(region.port_node(port), Some(a));
            assert_eq!(region.port_index(a, offset), Some(port));
        }

        // Global iterators
        let nodes = region.nodes_iter().collect_vec();
        assert_eq!(nodes.as_slice(), [root, a, b]);

        let ports = region.ports_iter().collect_vec();
        assert_eq!(ports.len(), region.port_count());

        assert_eq!(region, region.clone());

        // Links
        let a_o1 = region.output(a, 1).unwrap();
        let root_i0 = region.input(root, 0).unwrap();
        assert!(region.connected(a, root));
        assert_eq!(region.link_count(), 1);
        assert_eq!(region.output_neighbours(a).collect_vec().as_slice(), [root]);
        assert_eq!(
            region.output_links(a).collect_vec().as_slice(),
            [(a_o1, root_i0)]
        );
        assert_eq!(
            region.port_links(a_o1).collect_vec().as_slice(),
            [(a_o1, root_i0)]
        );
        assert_eq!(
            region.all_links(root).collect_vec().as_slice(),
            [(root_i0, a_o1)]
        );
        assert_eq!(
            region.get_connections(a, root).collect_vec().as_slice(),
            [(a_o1, root_i0)]
        );
        assert_eq!(region.get_connections(b, a).count(), 0);
        assert_eq!(region.all_neighbours(root).collect_vec().as_slice(), [a]);

        // Multiports
        let multigraph = MultiPortGraph::from(graph);
        let region = FlatRegion::new(&multigraph, &hierarchy, root);
        let a_o1 = SubportIndex::new_unique(a_o1);
        assert_eq!(
            region.all_subports(a).collect_vec(),
            multigraph.all_subports(a).collect_vec()
        );
        assert_eq!(
            region.subports(a, Direction::Incoming).collect_vec(),
            multigraph.subports(a, Direction::Incoming).collect_vec()
        );
        assert_eq!(region.subport_link(a_o1), multigraph.subport_link(a_o1));

        Ok(())
    }
}
