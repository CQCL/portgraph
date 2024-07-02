//! Lowest common ancestor algorithm on hierarchy forests.

use crate::{Hierarchy, NodeIndex, PortView, UnmanagedDenseMap};

/// Constructs a data structure that allows efficient queries of the lowest
/// common ancestor of two nodes in a hierarchy forest.
///
/// Given two nodes `a` and `b`, the lowest common ancestor is the node that is
/// an ancestor of both `a` and `b` and has the greatest depth.
///
/// This algorithm is based on binary lifting. The precomputation takes
/// `O(n log n)` time, where `n` is the number of nodes in the hierarchy.
/// Each `LCA::lca` query takes `O(log n)` time.
pub fn lca(graph: impl PortView, hierarchy: &Hierarchy) -> LCA {
    LCA::new(graph, hierarchy)
}

/// A precomputed data structure for lowest common ancestor queries between
/// nodes in a hierarchy.
#[derive(Debug, Default, Clone)]
pub struct LCA {
    /// For each node, stores the timestamp of the first visit in a depth-first
    /// traversal of the hierarchy.
    first_visit: UnmanagedDenseMap<NodeIndex, usize>,
    /// For each node, stores the timestamp of the last visit in a depth-first
    /// traversal of the hierarchy.
    last_visit: UnmanagedDenseMap<NodeIndex, usize>,
    /// For each node, stores the 1st, 2nd, 4th, 8th, ... ancestor.
    climb_nodes: UnmanagedDenseMap<NodeIndex, Vec<NodeIndex>>,
}

impl LCA {
    /// Initializes the lowest common ancestor data structure.
    ///
    /// Complexity: O(n log n)
    pub fn new(graph: impl PortView, hierarchy: &Hierarchy) -> Self {
        let capacity = graph.node_capacity();
        let mut lca = LCA {
            first_visit: UnmanagedDenseMap::with_capacity(capacity),
            last_visit: UnmanagedDenseMap::with_capacity(capacity),
            climb_nodes: UnmanagedDenseMap::with_capacity(capacity),
        };

        // Traverse the hierarchy in a depth-first order, filling the
        // `first_visit`, and `last_visit` arrays.
        let mut timestamp = 0;
        let mut stack = vec![];
        for root in graph.nodes_iter() {
            // We start with an empty stack
            debug_assert!(stack.is_empty());

            if !hierarchy.is_root(root) {
                continue;
            }
            stack.push(DFSState::Visit {
                node: root,
                parent: None,
            });
            while let Some(state) = stack.pop() {
                match state {
                    DFSState::Visit { node, parent } => {
                        lca.first_visit[node] = timestamp;
                        timestamp += 1;

                        // Compute the climb nodes.
                        // That is, the 1st, 2nd, 4th, 8th, ... ancestor.
                        if let Some(parent) = parent {
                            let mut climb = vec![parent];
                            let mut prev = parent;
                            for i in 1.. {
                                let Some(&u) = lca.climb_nodes[prev].get(i - 1) else {
                                    break;
                                };
                                climb.push(u);
                                prev = u;
                            }
                            lca.climb_nodes[node] = climb;
                        }

                        stack.push(DFSState::Finish { node });
                        for child in hierarchy.children(node) {
                            stack.push(DFSState::Visit {
                                node: child,
                                parent: Some(node),
                            });
                        }
                    }
                    DFSState::Finish { node } => {
                        lca.last_visit[node] = timestamp;
                        timestamp += 1;
                    }
                }
            }
        }

        lca
    }

    /// Returns `true` if `a` is an ancestor of `b` in the hierarchy.
    ///
    /// If `a` and `b` are the same node, returns `true`.
    ///
    /// Complexity: O(1)
    pub fn is_ancestor(&self, a: NodeIndex, b: NodeIndex) -> bool {
        self.first_visit[a] <= self.first_visit[b] && self.last_visit[a] >= self.last_visit[b]
    }

    /// Returns the root of the hierarchy that contains the given node.
    ///
    /// Complexity: O(log n)
    pub fn root(&self, node: NodeIndex) -> NodeIndex {
        let mut u = node;
        while let Some(&v) = self.climb_nodes[u].last() {
            u = v;
        }
        u
    }

    /// Given two nodes, returns the lowest common ancestor in the hierarchy.
    ///
    /// If the nodes are not in the same tree, returns `None`.
    ///
    /// Complexity: O(log n)
    pub fn lca(&self, a: NodeIndex, b: NodeIndex) -> Option<NodeIndex> {
        if self.is_ancestor(a, b) {
            return Some(a);
        }
        if self.is_ancestor(b, a) {
            return Some(b);
        }
        // The nodes are in different trees.
        if self.root(a) != self.root(b) {
            return None;
        }

        // Search the ancestors of `a` to find the lowest common ancestor with `b`.
        // We start by finding an ancestor of `a` that is not an ancestor of `b`,
        // but has an ancestor in its climb nodes. We call this node `u`.
        //
        // Once we find this, we can do binary search on the nodes to find the LCA.

        // Invariant: `u` is an ancestor of `a` (or `a`), but not an ancestor of `b`.
        //
        // Find a `u` where the last ancestor is an ancestor of `b`.
        let mut u = itertools::iterate(Some(a), |u| {
            u.and_then(|u| self.climb_nodes[u].last().copied())
        })
        .take_while(|u| u.is_some_and(|u| !self.is_ancestor(u, b)))
        .last()??;

        // Invariant: The 2^i ancestor of `u` is an ancestor of `b`.
        //
        // Do a binary search on the ancestors to find the LCA.
        // On each iteration, we start by knowing that the LCA is in the `2^i` ancestors of `u`.
        // We then decrement `i` and update `u` if needed.
        let mut i = self.climb_nodes[u].len() - 1;
        while i > 0 {
            i -= 1;
            // The updated 2^i ancestor of `u`. This is the middle point of the binary search.
            let v = self.climb_nodes[u][i];
            if !self.is_ancestor(v, b) {
                // The 2^i ancestor of `u` is not an ancestor of `b` so the LCA must be between
                // the 2^i and 2^{i+1} ancestor of `u`. Hence update `u` to the 2^i ancestor.
                u = v;
                // Ensure `i` is within bounds.
                i = i.max(self.climb_nodes[u].len() - 1);
            }
        }

        Some(self.climb_nodes[u][0])
    }
}

/// States for the depth-first search ran during the precomputation of the
/// LCA data structure.
#[derive(Debug, Clone, Copy, Hash)]
enum DFSState {
    /// Visit a node for the first time.
    Visit {
        node: NodeIndex,
        parent: Option<NodeIndex>,
    },
    /// Return from visiting a node.
    Finish { node: NodeIndex },
}

#[cfg(test)]
mod test {
    use crate::{PortGraph, PortMut};

    use super::*;
    use rstest::{fixture, rstest};

    /// A simple hierarchy with some nodes and edges.
    #[fixture]
    fn test_hierarchy() -> (PortGraph, Hierarchy) {
        let mut graph = PortGraph::with_capacity(16, 0);
        for _ in 0..16 {
            graph.add_node(0, 0);
        }

        let mut hier = Hierarchy::with_capacity(16);

        let edges = [
            // 0 -> {
            //   1 -> {
            //     3 -> 4 -> 5 -> 6,
            //     7,
            //   },
            //   2 -> 8 -> {9, 10},
            // }
            (0, 1),
            (0, 2),
            (1, 3),
            (3, 4),
            (4, 5),
            (5, 6),
            (1, 7),
            (2, 8),
            (8, 9),
            (8, 10),
            // 11 -> {12, 13}
            (11, 12),
            (11, 13),
            // 14 and 15 are independent nodes.
        ];
        for (parent, node) in edges {
            hier.push_child(NodeIndex::new(node), NodeIndex::new(parent))
                .unwrap();
        }

        (graph, hier)
    }

    #[rstest]
    fn lca(test_hierarchy: (PortGraph, Hierarchy)) {
        let lca = LCA::new(&test_hierarchy.0, &test_hierarchy.1);

        // Little helper to convert node indexes.
        let n = NodeIndex::new;

        assert_eq!(lca.lca(n(5), n(10)), Some(n(0)));
        assert_eq!(lca.lca(n(10), n(5)), Some(n(0)));
        assert_eq!(lca.lca(n(6), n(10)), Some(n(0)));
        assert_eq!(lca.lca(n(10), n(6)), Some(n(0)));

        // Test the roots
        for node in 0..=10 {
            assert_eq!(lca.root(n(node)), n(0));
        }
        for node in 11..=13 {
            assert_eq!(lca.root(n(node)), n(11));
        }
        for node in 14..=15 {
            assert_eq!(lca.root(n(node)), n(node));
        }

        // Test the lowest common ancestors
        assert_eq!(lca.lca(n(0), n(0)), Some(n(0)));
        assert_eq!(lca.lca(n(0), n(1)), Some(n(0)));
        assert_eq!(lca.lca(n(0), n(9)), Some(n(0)));
        assert_eq!(lca.lca(n(1), n(0)), Some(n(0)));
        assert_eq!(lca.lca(n(9), n(0)), Some(n(0)));
        assert_eq!(lca.lca(n(0), n(11)), None);
        assert_eq!(lca.lca(n(0), n(12)), None);
        assert_eq!(lca.lca(n(0), n(14)), None);
        assert_eq!(lca.lca(n(11), n(0)), None);
        assert_eq!(lca.lca(n(12), n(0)), None);
        assert_eq!(lca.lca(n(14), n(0)), None);

        assert_eq!(lca.lca(n(14), n(14)), Some(n(14)));
        assert_eq!(lca.lca(n(14), n(15)), None);

        assert_eq!(lca.lca(n(1), n(2)), Some(n(0)));
        assert_eq!(lca.lca(n(7), n(8)), Some(n(0)));
        assert_eq!(lca.lca(n(7), n(10)), Some(n(0)));
        assert_eq!(lca.lca(n(10), n(7)), Some(n(0)));
        assert_eq!(lca.lca(n(5), n(9)), Some(n(0)));
        assert_eq!(lca.lca(n(9), n(5)), Some(n(0)));
        assert_eq!(lca.lca(n(6), n(9)), Some(n(0)));
        assert_eq!(lca.lca(n(9), n(6)), Some(n(0)));

        assert_eq!(lca.lca(n(2), n(10)), Some(n(2)));
        assert_eq!(lca.lca(n(10), n(2)), Some(n(2)));

        assert_eq!(lca.lca(n(9), n(12)), None);
    }
}
