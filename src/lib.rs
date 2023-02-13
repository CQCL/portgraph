use std::num::NonZeroU32;

//pub mod dot;
#[allow(clippy::module_inception)]
pub mod graph;
pub mod hierarchy;
//pub mod substitute;
pub mod toposort;
pub mod unweighted;
pub mod weights;

#[cfg(feature = "pyo3")]
pub mod py_graph;

pub use crate::graph::Graph;
pub use crate::graph::PortGraph;
pub use crate::unweighted::UnweightedGraph;

#[cfg_attr(feature = "pyo3", pyclass)]
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Direction {
    Incoming = 0,
    Outgoing = 1,
}

impl Default for Direction {
    #[inline(always)]
    fn default() -> Self {
        Direction::Incoming
    }
}

impl Direction {
    #[inline(always)]
    pub fn index(self) -> usize {
        self as usize
    }

    #[inline(always)]
    pub fn reverse(self) -> Direction {
        match self {
            Direction::Incoming => Direction::Outgoing,
            Direction::Outgoing => Direction::Incoming,
        }
    }
}

/// Incoming and outgoing.
pub const DIRECTIONS: [Direction; 2] = [Direction::Incoming, Direction::Outgoing];

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeIndex(NonZeroU32);

impl NodeIndex {
    #[inline]
    pub fn new(index: usize) -> Self {
        assert!(index < u32::MAX as usize);
        Self(unsafe { NonZeroU32::new_unchecked(1 + index as u32) })
    }

    #[inline]
    pub fn index(self) -> usize {
        u32::from(self.0) as usize - 1
    }
}

impl std::fmt::Debug for NodeIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // avoid unncessary newlines in alternate mode
        write!(f, "NodeIndex({})", self.index())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PortIndex(NonZeroU32);

impl PortIndex {
    #[inline]
    pub fn new(index: usize) -> Self {
        assert!(index < u32::MAX as usize);
        Self(unsafe { NonZeroU32::new_unchecked(1 + index as u32) })
    }

    #[inline]
    pub fn index(self) -> usize {
        u32::from(self.0) as usize - 1
    }
}

impl std::fmt::Debug for PortIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // avoid unncessary newlines in alternate mode
        write!(f, "PortIndex({})", self.index())
    }
}

pub type EdgeIndex = (PortIndex, PortIndex);

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashSet};

    use crate::{dot::dot_string, EdgeIndex, NodeIndex};

    use super::graph::Graph;

    #[test]
    fn test_insert_graph() {
        let mut g = Graph::<i8, i8>::with_capacity(3, 2);

        let e1 = g.add_edge(-1);
        let e2 = g.add_edge(-2);

        let _n0 = g.add_node_with_edges(0, [], [e1]).unwrap();
        let _n1 = g.add_node_with_edges(1, [e1], [e2]).unwrap();
        let _n2 = g.add_node_with_edges(2, [e2], []).unwrap();

        let mut g2 = Graph::<i8, i8>::with_capacity(2, 1);

        let e3 = g2.add_edge(-3); //(g20, 0), (g21, 0), -3);
        let _n3 = g2.add_node_with_edges(3, [], [e3]);
        let _n4 = g2.add_node_with_edges(4, [e3], []);

        g.insert_graph(g2);

        let correct_weights: HashSet<_> = HashSet::from_iter([0, 1, 2, 3, 4].into_iter());
        assert_eq!(
            HashSet::from_iter(g.node_weights().copied()),
            correct_weights
        );

        let correct_weights: HashSet<_> = HashSet::from_iter([-1, -2, -3].into_iter());
        assert_eq!(
            HashSet::from_iter(g.edge_weights().copied()),
            correct_weights
        );
    }

    #[test]
    fn test_remove_invalid() {
        let mut g = Graph::<i8, i8>::with_capacity(3, 2);

        let e1 = g.add_edge(-1);
        let e2 = g.add_edge(-2);
        let e3 = g.add_edge(-3);

        let _n0 = g.add_node_with_edges(0, [], [e1, e3]).unwrap();
        let n1 = g.add_node_with_edges(1, [e1], [e2]).unwrap();
        let _n2 = g.add_node_with_edges(2, [e2, e3], []).unwrap();

        assert_eq!(g.node_count(), 3);
        assert_eq!(g.edge_count(), 3);

        assert_eq!(g.remove_node(n1), Some(1));
        assert_eq!(g.remove_edge(e1), Some(-1));
        assert_eq!(g.remove_edge(e2), Some(-2));

        assert_eq!(g.node_count(), 2);
        assert_eq!(g.edge_count(), 1);

        let (nodemap, edgemap) = g.compact();

        assert_eq!(g.node_count(), 2);
        assert_eq!(g.edge_count(), 1);

        assert_eq!(
            nodemap,
            BTreeMap::from_iter([
                (NodeIndex::new(0), NodeIndex::new(0)),
                (NodeIndex::new(2), NodeIndex::new(1))
            ])
        );

        assert_eq!(
            edgemap,
            BTreeMap::from_iter([(EdgeIndex::new(2), EdgeIndex::new(0)),])
        );

        // TODO some better test of validity (check graph correctness conditions)
        let _s = dot_string(&g);
    }
}
