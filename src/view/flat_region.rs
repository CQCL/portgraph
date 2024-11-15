//! Views of a portgraph containing only the descendants of a node in a [`Hierarchy`].

use super::filter::NodeFiltered;
use crate::{Hierarchy, NodeIndex};

type FlatRegionContext<'g> = (&'g Hierarchy, NodeIndex);
type FlatRegionCallback<'g> = fn(NodeIndex, &FlatRegionContext<'g>) -> bool;

/// View of a portgraph containing only a root node and its direct children in a [`Hierarchy`].
///
/// For a view of all descendants, see [`crate::view::Region`].
pub type FlatRegion<'g, G> = NodeFiltered<G, FlatRegionCallback<'g>, FlatRegionContext<'g>>;

impl<'a, G> FlatRegion<'a, G>
where
    G: Clone,
{
    /// Create a new region view including all the descendants of the root node.
    pub fn new_flat_region(graph: G, hierarchy: &'a Hierarchy, root: NodeIndex) -> Self {
        let region_filter: FlatRegionCallback<'a> = |node, context| {
            let (hierarchy, root) = context;
            node == *root || hierarchy.parent(node) == Some(*root)
        };
        Self::new_node_filtered(graph, region_filter, (hierarchy, root))
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
}
