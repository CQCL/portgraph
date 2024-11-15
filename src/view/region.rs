//! Views of a portgraph containing only the descendants of a node in a [`Hierarchy`].

use delegate::delegate;
use itertools::Either;
use std::sync::RwLock;
use std::{collections::HashMap, iter};

use super::{LinkView, MultiView, PortView};
use crate::{Direction, Hierarchy, NodeIndex, PortIndex, PortOffset};

/// View of a portgraph containing only a root node and its descendants in a
/// [`Hierarchy`].
///
/// For a view of a portgraph containing only the root and its direct children,
/// see [`crate::view::FlatRegion`]. Prefer using the flat variant when possible, as it is
/// more efficient.
#[derive(Debug)]
pub struct Region<'g, G> {
    /// The base graph
    graph: G,
    /// The root node of the region
    region_root: NodeIndex,
    /// The graph's hierarchy
    hierarchy: &'g Hierarchy,
    /// Cache of the result of the [`is_descendant`] check.
    is_descendant: RwLock<HashMap<NodeIndex, bool>>,
}

impl<'g, G> Region<'g, G>
where
    G: Clone,
{
    /// Create a new [`Region`] looking at a `root` node and its descendants in a [`Hierarchy`].
    pub fn new(graph: G, hierarchy: &'g Hierarchy, root: NodeIndex) -> Self {
        let mut is_descendant = HashMap::new();
        is_descendant.insert(root, false);
        Self {
            graph,
            region_root: root,
            hierarchy,
            is_descendant: RwLock::new(is_descendant),
        }
    }

    /// Check if a node is a descendant of the root node.
    ///
    /// Caches the result of the check.
    pub fn is_descendant(&self, node: NodeIndex) -> bool {
        if node == self.region_root {
            return true;
        }

        // First, access the cache read-only to check if the node has already been visited.
        // And compute whether the node is a descendant otherwise.
        let (ancestors, is_descendant) = {
            let cache = self
                .is_descendant
                .read()
                .expect("The Region cache is poisoned.");

            if let Some(is_descendant) = cache.get(&node) {
                // We have already checked this node.
                return *is_descendant;
            }
            // Traverse the ancestors until we see a node we have already checked, or the root.
            let ancestors: Vec<_> = iter::successors(Some(node), |node| {
                let parent = self.hierarchy.parent(*node)?;
                match cache.contains_key(&parent) {
                    true => None,
                    false => Some(parent),
                }
            })
            .collect();
            let first_visited_ancestor = self.hierarchy.parent(*ancestors.last().unwrap());
            let is_descendant = first_visited_ancestor == Some(self.region_root)
                || first_visited_ancestor
                    .map_or(false, |ancestor| cache.get(&ancestor).copied().unwrap());
            drop(cache);
            (ancestors, is_descendant)
        };

        // Now lock the cache for writing and update it with the new information.
        let mut cache_mut = self
            .is_descendant
            .write()
            .expect("The Region cache is poisoned.");
        for node in ancestors {
            cache_mut.insert(node, is_descendant);
        }
        is_descendant
    }

    /// Get the root node of the region.
    pub fn region_root(&self) -> NodeIndex {
        self.region_root
    }
}

impl<'g, G> Region<'g, G>
where
    G: LinkView + Clone,
{
    /// Utility function to filter out links that are not in the subgraph.
    #[inline(always)]
    fn contains_link(&self, (from, to): (G::LinkEndpoint, G::LinkEndpoint)) -> bool {
        self.contains_endpoint(from) && self.contains_endpoint(to)
    }

    /// Utility function to filter out link endpoints that are not in the subgraph.
    #[inline(always)]
    fn contains_endpoint(&self, e: G::LinkEndpoint) -> bool {
        self.contains_port(e.into())
    }
}

impl<'g, G: PartialEq> PartialEq for Region<'g, G> {
    fn eq(&self, other: &Self) -> bool {
        self.region_root == other.region_root
            && self.graph == other.graph
            && self.hierarchy == other.hierarchy
    }
}

impl<'g, G: Clone> Clone for Region<'g, G> {
    fn clone(&self) -> Self {
        // Clone the cache if it is not currently locked.
        // Otherwise, create a new empty cache.
        let is_descendant = match self.is_descendant.try_read() {
            Ok(cache) => cache.clone(),
            Err(_) => HashMap::new(),
        };
        Self {
            graph: self.graph.clone(),
            region_root: self.region_root,
            hierarchy: self.hierarchy,
            is_descendant: RwLock::new(is_descendant),
        }
    }
}

impl<'g, G> PortView for Region<'g, G>
where
    G: PortView + Clone,
{
    #[inline(always)]
    fn contains_node(&'_ self, node: NodeIndex) -> bool {
        self.is_descendant(node)
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
        false
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
        self.hierarchy.descendants(self.region_root)
    }

    #[inline]
    fn ports_iter(&self) -> impl Iterator<Item = PortIndex> + Clone {
        self.nodes_iter().flat_map(|n| self.graph.all_ports(n))
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

impl<'g, G> LinkView for Region<'g, G>
where
    G: LinkView + Clone,
{
    type LinkEndpoint = G::LinkEndpoint;

    fn get_connections(
        &self,
        from: NodeIndex,
        to: NodeIndex,
    ) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone {
        if self.is_descendant(from) && self.is_descendant(to) {
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

impl<'g, G> MultiView for Region<'g, G>
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

    use crate::{Hierarchy, LinkMut, PortGraph, PortMut};

    use super::*;

    #[test]
    fn single_node_region() {
        let mut graph = PortGraph::new();
        let root = graph.add_node(0, 0);

        let hierarchy = Hierarchy::new();

        let region = Region::new(&graph, &hierarchy, root);
        assert_eq!(region.node_count(), 1);
        assert_eq!(region.port_count(), 0);
    }

    #[test]
    fn simple_region() -> Result<(), Box<dyn Error>> {
        let mut graph = PortGraph::new();
        let other = graph.add_node(42, 0);
        let root = graph.add_node(1, 0);
        let a = graph.add_node(1, 2);
        let b = graph.add_node(0, 0);
        let c = graph.add_node(0, 0);
        graph.link_nodes(a, 0, other, 0)?;

        let mut hierarchy = Hierarchy::new();
        hierarchy.push_child(a, root)?;
        hierarchy.push_child(b, root)?;
        hierarchy.push_child(c, b)?;

        let region = Region::new(&graph, &hierarchy, root);

        assert!(
            region.nodes_iter().eq([root, a, b, c]),
            "{:?} != [root, a,b,c]",
            region.nodes_iter().collect::<Vec<_>>()
        );
        assert_eq!(region.node_count(), 4);
        assert_eq!(region.port_count(), 4);
        assert_eq!(region.link_count(), 0);

        assert!(region.all_links(a).eq([]));
        assert!(region.all_neighbours(a).eq([]));

        Ok(())
    }
}
