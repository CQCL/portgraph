//! Views of a portgraph containing only the descendants of a node in a [`Hierarchy`].

use std::{cell::RefCell, collections::HashMap, iter};

use super::filter::NodeFiltered;
use crate::{Hierarchy, NodeIndex};

type RegionCallback<'g> = fn(NodeIndex, &RegionContext<'g>) -> bool;

/// View of a portgraph containing only a root node and its descendants in a
/// [`Hierarchy`].
///
/// For a view of a portgraph containing only the root and its direct children,
/// see [`FlatRegion`]. Prefer using the flat variant when possible, as it is
/// more efficient.
///
/// [`Region`] does not implement `Sync` as it uses a [`RefCell`] to cache the
/// node filtering.
pub type Region<'g, G> = NodeFiltered<'g, G, RegionCallback<'g>, RegionContext<'g>>;

impl<'a, G> Region<'a, G> {
    /// Create a new region view including all the descendants of the root node.
    pub fn new_region(graph: &'a G, hierarchy: &'a Hierarchy, root: NodeIndex) -> Self {
        let region_filter: RegionCallback<'a> =
            |node, context| node == context.root() || context.is_descendant(node);
        Self::new(graph, region_filter, RegionContext::new(hierarchy, root))
    }
}

/// Internal context used in the [`Region`] adaptor.
#[derive(Debug, Clone)]
pub struct RegionContext<'g> {
    hierarchy: &'g Hierarchy,
    root: NodeIndex,
    /// Cache of the result of the [`is_descendant`] check.
    is_descendant: RefCell<HashMap<NodeIndex, bool>>,
}

impl<'g> RegionContext<'g> {
    /// Create a new [`RegionContext`].
    pub fn new(hierarchy: &'g Hierarchy, root: NodeIndex) -> Self {
        let mut is_descendant = HashMap::new();
        is_descendant.insert(root, false);
        Self {
            hierarchy,
            root,
            is_descendant: RefCell::new(is_descendant),
        }
    }

    /// Check if a node is a descendant of the root node.
    ///
    /// Caches the result of the check.
    pub fn is_descendant(&self, node: NodeIndex) -> bool {
        if let Some(is_descendant) = self.is_descendant.borrow().get(&node) {
            // We have already checked this node.
            return *is_descendant;
        }
        // Traverse the ancestors until we see a node we have already checked.
        let cache = self.is_descendant.borrow();
        let ancestors: Vec<_> = iter::successors(Some(node), |node| {
            let parent = self.hierarchy.parent(*node)?;
            match cache.contains_key(&parent) {
                true => None,
                false => Some(parent),
            }
        })
        .collect();
        let first_visited_ancestor = self.hierarchy.parent(*ancestors.last().unwrap());
        let is_descendant = first_visited_ancestor == Some(self.root)
            || first_visited_ancestor
                .map_or(false, |ancestor| cache.get(&ancestor).copied().unwrap());
        drop(cache);

        // Update the cache for all the unvisited ancestors.
        let mut cache_mut = self.is_descendant.borrow_mut();
        for node in ancestors {
            cache_mut.insert(node, is_descendant);
        }
        is_descendant
    }

    /// Get the root node of the region.
    pub fn root(&self) -> NodeIndex {
        self.root
    }
}

type FlatRegionContext<'g> = (&'g Hierarchy, NodeIndex);
type FlatRegionCallback<'g> = fn(NodeIndex, &FlatRegionContext<'g>) -> bool;

/// View of a portgraph containing only a root node and its direct children in a [`Hierarchy`].
///
/// For a view of all descendants, see [`Region`].
pub type FlatRegion<'g, G> = NodeFiltered<'g, G, FlatRegionCallback<'g>, FlatRegionContext<'g>>;

impl<'a, G> FlatRegion<'a, G> {
    /// Create a new region view including all the descendants of the root node.
    pub fn new_flat_region(graph: &'a G, hierarchy: &'a Hierarchy, root: NodeIndex) -> Self {
        let region_filter: FlatRegionCallback<'a> = |node, context| {
            let (hierarchy, root) = context;
            node == *root || hierarchy.parent(node) == Some(*root)
        };
        Self::new(graph, region_filter, (hierarchy, root))
    }
}

#[cfg(test)]
mod test {
    use std::error::Error;

    use crate::{Hierarchy, LinkMut, LinkView, PortGraph, PortMut, PortView};

    use super::*;

    #[test]
    fn single_node_region() {
        let mut graph = PortGraph::new();
        let root = graph.add_node(0, 0);

        let hierarchy = Hierarchy::new();

        let region = FlatRegion::new_flat_region(&graph, &hierarchy, root);
        assert_eq!(region.node_count(), 1);
        assert_eq!(region.port_count(), 0);

        let region = Region::new_region(&graph, &hierarchy, root);
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

        let mut hierarchy = Hierarchy::new();
        hierarchy.push_child(a, root)?;
        hierarchy.push_child(b, root)?;
        hierarchy.push_child(c, b)?;

        let region = FlatRegion::new_flat_region(&graph, &hierarchy, root);

        assert!(region.nodes_iter().eq([root, a, b]));
        assert_eq!(region.node_count(), 3);
        assert_eq!(region.port_count(), 4);
        assert_eq!(region.link_count(), 0);

        assert!(region.all_links(a).eq([]));
        assert!(region.all_neighbours(a).eq([]));

        Ok(())
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

        let region = Region::new_region(&graph, &hierarchy, root);

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
