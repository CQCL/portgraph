//! View of a portgraph containing only the descendants of a node in a [`Hierarchy`].

use std::{cell::RefCell, collections::HashMap, iter};

use super::filter::NodeFiltered;
use crate::{Direction, Hierarchy, LinkView, MultiView, NodeIndex, PortIndex, PortView};

use delegate::delegate;

type RegionCallback<'g> = fn(NodeIndex, &RegionContext<'g>) -> bool;
type RegionInternalGraph<'g, G> = NodeFiltered<'g, G, RegionCallback<'g>, RegionContext<'g>>;

/// View of a portgraph containing only the descendants of a node in a
/// [`Hierarchy`].
///
/// For a view of a portgraph containing only the direct children of a node, see
/// [`FlatRegion`]. Prefer using [`FlatRegion`] if possible, as it is more
/// efficient.
///
/// [`Region`] does not implement `Sync` as it uses a [`RefCell`] to cache the
/// node filtering.
#[derive(Debug, Clone)]
pub struct Region<'g, G> {
    graph: RegionInternalGraph<'g, G>,
    root: NodeIndex,
}

impl<'a, G> Region<'a, G> {
    /// Create a new region view including all the descendants of the root node.
    pub fn new(graph: &'a G, hierarchy: &'a Hierarchy, root: NodeIndex) -> Self {
        let region_filter: RegionCallback<'a> = |node, context| context.is_descendant(node);
        Self {
            graph: NodeFiltered::new(graph, region_filter, RegionContext::new(hierarchy, root)),
            root,
        }
    }

    /// Get the root node of the region.
    pub fn root(&self) -> NodeIndex {
        self.root
    }
}

/// Internal context used in the [`Region`] iterators.
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

type FlatRegionContext<'g> = (&'g Hierarchy, NodeIndex);
type FlatRegionCallback<'g> = fn(NodeIndex, &FlatRegionContext<'g>) -> bool;
type FlatRegionInternalGraph<'g, G> =
    NodeFiltered<'g, G, FlatRegionCallback<'g>, FlatRegionContext<'g>>;

/// View of a portgraph containing only the direct children of a node in a [`Hierarchy`].
///
/// For a view of all descendants, see [`Region`].
#[derive(Debug, Clone, PartialEq)]
pub struct FlatRegion<'g, G> {
    graph: FlatRegionInternalGraph<'g, G>,
    root: NodeIndex,
}

impl<'a, G> FlatRegion<'a, G> {
    /// Create a new region view including all the descendants of the root node.
    pub fn new(graph: &'a G, hierarchy: &'a Hierarchy, root: NodeIndex) -> Self {
        let region_filter: FlatRegionCallback<'a> = |node, context| {
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

impl<'g, G> PortView for FlatRegion<'g, G>
where
    G: PortView,
{
    type Nodes<'a> = <FlatRegionInternalGraph<'g, G> as PortView>::Nodes<'a>
    where
        Self: 'a;

    type Ports<'a> = <FlatRegionInternalGraph<'g, G> as PortView>::Ports<'a>
    where
        Self: 'a;

    type NodePorts<'a> = <FlatRegionInternalGraph<'g, G> as PortView>::NodePorts<'a>
    where
        Self: 'a;

    type NodePortOffsets<'a> = <FlatRegionInternalGraph<'g, G> as PortView>::NodePortOffsets<'a>
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

impl<'g, G> LinkView for FlatRegion<'g, G>
where
    G: LinkView,
{
    type LinkEndpoint = G::LinkEndpoint;

    type Neighbours<'a> = <FlatRegionInternalGraph<'g, G> as LinkView>::Neighbours<'a>
    where
        Self: 'a;

    type NodeConnections<'a> = <FlatRegionInternalGraph<'g, G> as LinkView>::NodeConnections<'a>
    where
        Self: 'a;

    type NodeLinks<'a> = <FlatRegionInternalGraph<'g, G> as LinkView>::NodeLinks<'a>
    where
        Self: 'a;

    type PortLinks<'a> = <FlatRegionInternalGraph<'g, G> as LinkView>::PortLinks<'a>
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

impl<'g, G> MultiView for FlatRegion<'g, G>
where
    G: MultiView,
{
    type NodeSubports<'a> = <FlatRegionInternalGraph<'g, G> as MultiView>::NodeSubports<'a>
    where
        Self: 'a;

    delegate! {
            to self.graph {
        fn subport_link(&self, subport: Self::LinkEndpoint) -> Option<Self::LinkEndpoint>;
        fn subports(&self, node: NodeIndex, direction: Direction) -> Self::NodeSubports<'_>;
        fn all_subports(&self, node: NodeIndex) -> Self::NodeSubports<'_>;
    }}
}

#[cfg(test)]
mod test {
    use std::error::Error;

    use crate::{Hierarchy, LinkMut, PortGraph, PortMut};

    use super::*;

    #[test]
    fn empty_region() {
        let mut graph = PortGraph::new();
        let root = graph.add_node(0, 0);

        let hierarchy = Hierarchy::new();

        let region = FlatRegion::new(&graph, &hierarchy, root);
        assert!(region.is_empty());
        assert_eq!(region.node_count(), 0);
        assert_eq!(region.port_count(), 0);

        let region = Region::new(&graph, &hierarchy, root);
        assert!(region.is_empty());
        assert_eq!(region.node_count(), 0);
        assert_eq!(region.port_count(), 0);
    }

    #[test]
    fn simple_flat_region() -> Result<(), Box<dyn Error>> {
        let mut graph = PortGraph::new();
        let root = graph.add_node(42, 0);
        let a = graph.add_node(1, 2);
        let b = graph.add_node(0, 0);
        let c = graph.add_node(0, 0);
        graph.link_nodes(a, 0, root, 0)?;

        let mut hierarchy = Hierarchy::new();
        hierarchy.push_child(a, root)?;
        hierarchy.push_child(b, root)?;
        hierarchy.push_child(c, b)?;

        let region = FlatRegion::new(&graph, &hierarchy, root);

        assert!(region.nodes_iter().eq([a, b]));
        assert_eq!(region.node_count(), 2);
        assert_eq!(region.port_count(), 3);
        assert_eq!(region.link_count(), 0);

        assert!(region.all_links(a).eq([]));
        assert!(region.all_neighbours(a).eq([]));

        Ok(())
    }

    #[test]
    fn simple_region() -> Result<(), Box<dyn Error>> {
        let mut graph = PortGraph::new();
        let root = graph.add_node(42, 0);
        let a = graph.add_node(1, 2);
        let b = graph.add_node(0, 0);
        let c = graph.add_node(0, 0);
        graph.link_nodes(a, 0, root, 0)?;

        let mut hierarchy = Hierarchy::new();
        hierarchy.push_child(a, root)?;
        hierarchy.push_child(b, root)?;
        hierarchy.push_child(c, b)?;

        let region = Region::new(&graph, &hierarchy, root);

        assert!(
            region.nodes_iter().eq([a, b, c]),
            "{:?} != [a,b,c]",
            region.nodes_iter().collect::<Vec<_>>()
        );
        assert_eq!(region.node_count(), 3);
        assert_eq!(region.port_count(), 3);
        assert_eq!(region.link_count(), 0);

        assert!(region.all_links(a).eq([]));
        assert!(region.all_neighbours(a).eq([]));

        Ok(())
    }
}
