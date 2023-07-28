//! Convexity checking for portgraphs.
//!
//! This is based on a [`ConvexChecker`] object that is expensive to create
//! (linear in the size of the graph), but can be reused to check multiple
//! subgraphs for convexity quickly.

use std::collections::{BTreeMap, BTreeSet};

use crate::algorithms::toposort;
use crate::{Direction, LinkView, NodeIndex};

use super::TopoSort;

#[derive(Default, Clone, Debug, PartialEq, Eq)]
enum Causal {
    #[default]
    P, // in the past
    F, // in the future
}

/// A pre-computed datastructure for fast convexity checking.
///
/// TODO: implement for graph traits?
pub struct ConvexChecker<G> {
    graph: G,
    // The nodes in topological order
    topsort_nodes: Vec<NodeIndex>,
    // The index of a node in the topological order (the inverse of topsort_nodes)
    topsort_ind: BTreeMap<NodeIndex, usize>,
    // A temporary datastructure used during `is_convex`
    causal: Vec<Causal>,
}

impl<G> ConvexChecker<G>
where
    G: LinkView + Copy,
{
    /// Create a new ConvexChecker
    pub fn new(graph: G) -> Self {
        let inputs = graph.nodes_iter().filter(|&n| graph.num_inputs(n) == 0);
        let topsort: TopoSort<_> = toposort(graph, inputs, Direction::Outgoing);
        let topsort_nodes: Vec<_> = topsort.collect();
        let flip = |(i, &n)| (n, i);
        let topsort_ind = topsort_nodes.iter().enumerate().map(flip).collect();
        let causal = vec![Causal::default(); topsort_nodes.len()];
        Self {
            graph,
            topsort_nodes,
            topsort_ind,
            causal,
        }
    }

    /// Whether the set of nodes are convex
    pub fn is_convex(&mut self, nodes: impl IntoIterator<Item = NodeIndex>) -> bool {
        let nodes: BTreeSet<_> = nodes.into_iter().map(|n| self.topsort_ind[&n]).collect();
        let min_ind = *nodes.first().unwrap();
        let max_ind = *nodes.last().unwrap();
        for ind in min_ind..=max_ind {
            let n = self.topsort_nodes[ind];
            let mut in_inds = {
                let in_neighs = self.graph.input_neighbours(n);
                in_neighs
                    .map(|n| self.topsort_ind[&n])
                    .filter(|&ind| ind >= min_ind)
            };
            if nodes.contains(&ind) {
                if in_inds.any(|ind| self.causal[ind] == Causal::F) {
                    // There is a node in the past that is also in the future!
                    return false;
                }
                self.causal[ind] = Causal::P;
            } else {
                self.causal[ind] = match in_inds
                    .any(|ind| nodes.contains(&ind) || self.causal[ind] == Causal::F)
                {
                    true => Causal::F,
                    false => Causal::P,
                };
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use crate::{LinkMut, PortGraph, PortMut};

    use super::ConvexChecker;

    #[test]
    fn convexity_test() {
        let mut g = PortGraph::new();
        let i1 = g.add_node(0, 2);
        let i2 = g.add_node(0, 1);
        let i3 = g.add_node(0, 1);

        let n1 = g.add_node(2, 2);
        g.link_nodes(i1, 0, n1, 0).unwrap();
        g.link_nodes(i2, 0, n1, 1).unwrap();

        let n2 = g.add_node(2, 2);
        g.link_nodes(i1, 1, n2, 0).unwrap();
        g.link_nodes(i3, 0, n2, 1).unwrap();

        let o1 = g.add_node(2, 0);
        g.link_nodes(n1, 0, o1, 0).unwrap();
        g.link_nodes(n2, 0, o1, 1).unwrap();

        let o2 = g.add_node(2, 0);
        g.link_nodes(n1, 1, o2, 0).unwrap();
        g.link_nodes(n2, 1, o2, 1).unwrap();

        let mut checker = ConvexChecker::new(&g);

        assert!(checker.is_convex(vec![i1, i2, i3]));
        assert!(checker.is_convex(vec![i1, n2]));
        assert!(!checker.is_convex(vec![i1, n2, o2]));
        assert!(!checker.is_convex(vec![i1, n2, o1]));
        assert!(checker.is_convex(vec![i1, n2, o1, n1]));
        assert!(checker.is_convex(vec![i1, n2, o2, n1]));
        assert!(checker.is_convex(vec![i1, i3, n2]));
        assert!(!checker.is_convex(vec![i1, i3, o2]));
    }
}
