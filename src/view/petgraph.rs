//! Petgraph's trait implementations for portgraphs.

use std::iter::FusedIterator;

use bitvec::vec::BitVec;

use crate::multiportgraph::MultiPortGraph;
use crate::view::filter::{NodeFilter, NodeFiltered};
use crate::{LinkView, NodeIndex, PortGraph, PortView, SecondaryMap};

impl From<petgraph::Direction> for crate::Direction {
    fn from(d: petgraph::Direction) -> Self {
        match d {
            petgraph::Direction::Incoming => crate::Direction::Incoming,
            petgraph::Direction::Outgoing => crate::Direction::Outgoing,
        }
    }
}

impl From<crate::Direction> for petgraph::Direction {
    fn from(d: crate::Direction) -> Self {
        match d {
            crate::Direction::Incoming => petgraph::Direction::Incoming,
            crate::Direction::Outgoing => petgraph::Direction::Outgoing,
        }
    }
}

impl petgraph::visit::NodeRef for NodeIndex {
    type NodeId = NodeIndex;
    type Weight = ();

    fn id(&self) -> Self::NodeId {
        *self
    }

    fn weight(&self) -> &Self::Weight {
        &()
    }
}

/// Implement petgraph traits for a portgraph type or wrapper.
///
/// Can be called simply as `impl_petgraph_traits!(MyGraph)` for non-generic
/// graphs, or
/// ```ignore
/// impl_petgraph_traits!(MyGraph<T, G>, [T, G] where T: Bound, G: OtherBound);
/// ```
/// for generic types with bounds.
macro_rules! impl_petgraph_traits {
    ($graph:ty) => {impl_petgraph_traits!($graph, []);};
    ($graph:ty, [$($args:tt)*]) => {impl_petgraph_traits!($graph, [$($args)*] where );};
    ($graph:ty, [$($args:tt)*] where $($where:tt)*) => {
        impl<$($args)*> petgraph::visit::GraphBase for $graph where $($where)* {
            type NodeId = NodeIndex;
            type EdgeId = (
                <$graph as LinkView>::LinkEndpoint,
                <$graph as LinkView>::LinkEndpoint,
            );
        }

        impl<$($args)*> petgraph::visit::GraphProp for $graph where $($where)* {
            type EdgeType = petgraph::Directed;
        }

        impl<$($args)*> petgraph::visit::NodeCount for $graph where $($where)* {
            fn node_count(&self) -> usize {
                PortView::node_count(self)
            }
        }

        impl<$($args)*> petgraph::visit::NodeIndexable for $graph where $($where)* {
            fn node_bound(&self) -> usize {
                PortView::node_count(self)
            }

            fn to_index(&self, ix: Self::NodeId) -> usize {
                ix.index()
            }

            fn from_index(&self, ix: usize) -> Self::NodeId {
                NodeIndex::new(ix)
            }
        }

        impl<$($args)*> petgraph::visit::EdgeCount for $graph where $($where)* {
            fn edge_count(&self) -> usize {
                LinkView::link_count(self)
            }
        }

        impl<$($args)*> petgraph::visit::Data for $graph where $($where)* {
            type NodeWeight = ();
            type EdgeWeight = ();
        }

        impl<'g, $($args)*> petgraph::visit::IntoNodeIdentifiers for &'g $graph where $($where)* {
            type NodeIdentifiers = <$graph as PortView>::Nodes<'g>;

            fn node_identifiers(self) -> Self::NodeIdentifiers {
                self.nodes_iter()
            }
        }

        impl<'g, $($args)*> petgraph::visit::IntoNodeReferences for &'g $graph where $($where)* {
            type NodeRef = NodeIndex;
            type NodeReferences = <$graph as PortView>::Nodes<'g>;

            fn node_references(self) -> Self::NodeReferences {
                self.nodes_iter()
            }
        }

        impl<'g, $($args)*> petgraph::visit::IntoNeighbors for &'g $graph where $($where)* {
            type Neighbors = <$graph as LinkView>::Neighbours<'g>;

            fn neighbors(self, n: Self::NodeId) -> Self::Neighbors {
                self.all_neighbours(n)
            }
        }

        impl<'g, $($args)*> petgraph::visit::IntoNeighborsDirected for &'g $graph where $($where)* {
            type NeighborsDirected = <$graph as LinkView>::Neighbours<'g>;

            fn neighbors_directed(
                self,
                n: Self::NodeId,
                d: petgraph::Direction,
            ) -> Self::NeighborsDirected {
                self.neighbours(n, d.into())
            }
        }

        impl<'g, $($args)*> petgraph::visit::IntoEdgeReferences for &'g $graph where $($where)* {
            type EdgeRef = EdgeRef<<$graph as LinkView>::LinkEndpoint>;
            type EdgeReferences = EdgeRefs<'g, $graph>;

            fn edge_references(self) -> Self::EdgeReferences {
                EdgeRefs::new(self)
            }
        }

        impl<'g, $($args)*> petgraph::visit::IntoEdges for &'g $graph where $($where)* {
            type Edges = NodeEdgeRefs<'g, $graph>;

            fn edges(self, n: Self::NodeId) -> Self::Edges {
                NodeEdgeRefs::new(self, n)
            }
        }

        impl<'g, $($args)*> petgraph::visit::IntoEdgesDirected for &'g $graph where $($where)* {
            type EdgesDirected = NodeEdgeRefs<'g, $graph>;

            fn edges_directed(
                self,
                n: Self::NodeId,
                d: petgraph::Direction,
            ) -> Self::EdgesDirected {
                NodeEdgeRefs::new_directed(self, n, d.into())
            }
        }
    };
}

/// Implement petgraph's `Visitable` and `GetAdjacencyMatrix` traits for a portgraph type or wrapper.
///
/// Assumes that the node indices are dense and start at 0, and uses internal containers that consume O(#nodes) memory.
macro_rules! impl_visit_dense {
    ($graph:ty) => {impl_visit_dense!($graph, []);};
    ($graph:ty, [$($args:tt)*]) => {impl_visit_dense!($graph, [$($args)*] where );};
    ($graph:ty, [$($args:tt)*] where $($where:tt)*) => {
        impl<$($args)*> petgraph::visit::Visitable for $graph $($where)* {
            type Map = bitvec::vec::BitVec;

            fn visit_map(&self) -> Self::Map {
                BitVec::with_capacity(self.node_capacity())
            }

            fn reset_map(&self, map: &mut Self::Map) {
                map.clear();
            }
        }

        impl<$($args)*> petgraph::visit::GetAdjacencyMatrix for $graph $($where)* {
            type AdjMatrix = (bitvec::vec::BitVec, usize);

            fn adjacency_matrix(&self) -> Self::AdjMatrix {
                let row_size = self.node_capacity();
                let mut matrix = bitvec::bitvec![0; row_size * row_size];
                for node in self.nodes_iter() {
                    for neighbour in self.output_neighbours(node) {
                        let row = node.index();
                        let column = neighbour.index();
                        matrix.set(row * row_size + column, true);
                    }
                }
                (matrix, row_size)
            }

            fn is_adjacent(
                &self,
                matrix: &Self::AdjMatrix,
                a: Self::NodeId,
                b: Self::NodeId,
            ) -> bool {
                let (matrix, row_size) = matrix;
                let row = a.index();
                let column = b.index();
                matrix[row * row_size + column]
            }
        }
    };
}

/// Implement petgraph's `Visitable` and `GetAdjacencyMatrix` traits for a sparse portgraph type or wrapper.
///
/// Uses sparse containers to keep track of visited nodes.
macro_rules! impl_visit_sparse {
    ($graph:ty) => {impl_visit_sparse!($graph, []);};
    ($graph:ty, [$($args:tt)*]) => {impl_visit_sparse!($graph, [$($args)*] where );};
    ($graph:ty, [$($args:tt)*] where $($where:tt)*) => {
        impl<$($args)*> petgraph::visit::Visitable for $graph where $($where)* {
            type Map = std::collections::HashSet<Self::NodeId>;

            fn visit_map(&self) -> Self::Map {
                std::collections::HashSet::new()
            }

            fn reset_map(&self, map: &mut Self::Map) {
                map.clear();
            }
        }

        impl<$($args)*> petgraph::visit::GetAdjacencyMatrix for $graph where $($where)* {
            type AdjMatrix = std::collections::HashSet<(Self::NodeId, Self::NodeId)>;

            fn adjacency_matrix(&self) -> Self::AdjMatrix {
                let mut matrix = std::collections::HashSet::new();
                for node in self.nodes_iter() {
                    for neighbour in self.output_neighbours(node) {
                        matrix.insert((node, neighbour));
                    }
                }
                matrix
            }

            fn is_adjacent(
                &self,
                matrix: &Self::AdjMatrix,
                a: Self::NodeId,
                b: Self::NodeId,
            ) -> bool {
                matrix.contains(&(a, b))
            }
        }
    };
}

impl_petgraph_traits!(PortGraph);
impl_petgraph_traits!(MultiPortGraph);
impl_petgraph_traits!(NodeFiltered<'a, G, NodeFilter<Ctx>, Ctx>, ['a, G, Ctx]
    where
        G: LinkView,
        <G as LinkView>::LinkEndpoint: Eq
);

impl_visit_dense!(PortGraph);
impl_visit_dense!(MultiPortGraph);
impl_visit_sparse!(NodeFiltered<'a, G, NodeFilter<Ctx>, Ctx>, ['a, G, Ctx]
    where
        G: LinkView,
        <G as LinkView>::LinkEndpoint: Eq
);

impl petgraph::visit::VisitMap<NodeIndex> for BitVec {
    fn visit(&mut self, a: NodeIndex) -> bool {
        let is_visited = self.is_visited(&a);
        <Self as SecondaryMap<NodeIndex, bool>>::set(self, a, true);
        is_visited
    }

    fn is_visited(&self, a: &NodeIndex) -> bool {
        *<Self as SecondaryMap<NodeIndex, bool>>::get(self, *a)
    }
}

/// A reference to an edge in a portgraph, with information about the nodes it
/// connects.
///
/// Used to implement petgraph's `EdgeRef` trait.
#[derive(Debug, Clone, Copy)]
pub struct EdgeRef<P> {
    from_node: NodeIndex,
    to_node: NodeIndex,
    edge: (P, P),
}

impl<P> petgraph::visit::EdgeRef for EdgeRef<P>
where
    P: Copy,
{
    type NodeId = NodeIndex;
    type EdgeId = (P, P);
    type Weight = ();

    fn source(&self) -> Self::NodeId {
        self.from_node
    }

    fn target(&self) -> Self::NodeId {
        self.to_node
    }

    fn weight(&self) -> &Self::Weight {
        &()
    }

    fn id(&self) -> Self::EdgeId {
        self.edge
    }
}

/// Iterator over the edges of a portgraph.
///
/// Used for compatibility with petgraph.
pub struct EdgeRefs<'g, G: LinkView> {
    graph: &'g G,
    ports: G::Ports<'g>,
    links: Option<G::PortLinks<'g>>,
    count: usize,
}

impl<'g, G> EdgeRefs<'g, G>
where
    G: LinkView,
{
    /// Create a new iterator over the edges of a portgraph.
    pub fn new(graph: &'g G) -> Self {
        Self {
            graph,
            ports: graph.ports_iter(),
            links: None,
            count: graph.link_count(),
        }
    }
}

impl<'g, G> Iterator for EdgeRefs<'g, G>
where
    G: LinkView,
{
    type Item = EdgeRef<G::LinkEndpoint>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((from, to)) = self.links.as_mut().and_then(|links| links.next()) {
                return Some(EdgeRef {
                    from_node: self.graph.port_node(from).unwrap(),
                    to_node: self.graph.port_node(to).unwrap(),
                    edge: (from, to),
                });
            }

            let port = self.ports.next()?;
            self.links = Some(self.graph.port_links(port));
        }
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.count
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<G: LinkView> ExactSizeIterator for EdgeRefs<'_, G> {
    #[inline]
    fn len(&self) -> usize {
        self.count
    }
}

impl<G: LinkView> FusedIterator for EdgeRefs<'_, G> {}

/// Iterator over the edges of a node.
///
/// Used for compatibility with petgraph.
pub struct NodeEdgeRefs<'g, G: LinkView> {
    graph: &'g G,
    links: G::NodeLinks<'g>,
}

impl<'g, G> NodeEdgeRefs<'g, G>
where
    G: LinkView,
{
    /// Create a new iterator over the edges of a portgraph.
    pub fn new(graph: &'g G, node: NodeIndex) -> Self {
        Self {
            graph,
            links: graph.all_links(node),
        }
    }

    /// Create a new iterator over the edges of a portgraph.
    pub fn new_directed(graph: &'g G, node: NodeIndex, dir: crate::Direction) -> Self {
        Self {
            graph,
            links: graph.links(node, dir),
        }
    }
}

impl<'g, G> Iterator for NodeEdgeRefs<'g, G>
where
    G: LinkView,
{
    type Item = EdgeRef<G::LinkEndpoint>;

    fn next(&mut self) -> Option<Self::Item> {
        let (from, to) = self.links.next()?;
        Some(EdgeRef {
            from_node: self.graph.port_node(from).unwrap(),
            to_node: self.graph.port_node(to).unwrap(),
            edge: (from, to),
        })
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.links.count()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.links.size_hint()
    }
}

impl<'g, G: LinkView> ExactSizeIterator for NodeEdgeRefs<'g, G>
where
    G::NodeLinks<'g>: ExactSizeIterator,
{
    #[inline]
    fn len(&self) -> usize {
        self.links.len()
    }
}

impl<'g, G: LinkView> FusedIterator for NodeEdgeRefs<'g, G> where G::NodeLinks<'g>: FusedIterator {}
