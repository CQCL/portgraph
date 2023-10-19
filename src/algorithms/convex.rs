//! Convexity checking for portgraphs.
//!
//! This is based on a [`ConvexChecker`] object that is expensive to create
//! (linear in the size of the graph), but can be reused to check multiple
//! subgraphs for convexity quickly.

use std::collections::BTreeSet;

use bitvec::bitvec;
use bitvec::vec::BitVec;

use crate::algorithms::toposort;
use crate::{Direction, LinkView, NodeIndex, PortIndex, SecondaryMap, UnmanagedDenseMap};

use super::TopoSort;

/// A pre-computed data structure for fast convexity checking.
pub struct ConvexChecker<G> {
    graph: G,
    // The nodes in topological order
    topsort_nodes: Vec<NodeIndex>,
    // The index of a node in the topological order (the inverse of topsort_nodes)
    topsort_ind: UnmanagedDenseMap<NodeIndex, usize>,
    // A temporary data structure used during `is_convex`
    causal: CausalVec,
}

impl<G> ConvexChecker<G>
where
    G: LinkView + Clone,
{
    /// Create a new ConvexChecker.
    pub fn new(graph: G) -> Self {
        let inputs = graph
            .nodes_iter()
            .filter(|&n| graph.input_neighbours(n).count() == 0);
        let topsort: TopoSort<_> = toposort(graph.clone(), inputs, Direction::Outgoing);
        let topsort_nodes: Vec<_> = topsort.collect();
        let mut topsort_ind = UnmanagedDenseMap::with_capacity(graph.node_count());
        for (i, &n) in topsort_nodes.iter().enumerate() {
            topsort_ind.set(n, i);
        }
        let causal = CausalVec::new(topsort_nodes.len());
        Self {
            graph,
            topsort_nodes,
            topsort_ind,
            causal,
        }
    }

    /// The graph on which convexity queries can be made.
    pub fn graph(&self) -> G {
        self.graph.clone()
    }

    /// Whether the subgraph induced by the node set is convex.
    ///
    /// An induced subgraph is convex if there is no node that is both in the
    /// past and in the future of another node of the subgraph.
    ///
    /// This function requires mutable access to `self` because it uses a
    /// temporary data structure within the object.
    ///
    /// ## Arguments
    ///
    /// - `nodes`: The nodes inducing a subgraph of `self.graph()`.
    ///
    /// ## Algorithm
    ///
    /// Each node in the "vicinity" of the subgraph will be assigned a causal
    /// property, either of being in the past or in the future of the subgraph.
    /// It can then be checked whether there is a node in the past that is also
    /// in the future, violating convexity.
    ///
    /// Currently, the "vicinity" of a subgraph is defined as the set of nodes
    /// that are in the interval between the first and last node of the subgraph
    /// in some topological order. In the worst case this will traverse every
    /// node in the graph and can be improved on in the future.
    pub fn is_node_convex(&mut self, nodes: impl IntoIterator<Item = NodeIndex>) -> bool {
        let nodes: BTreeSet<_> = nodes.into_iter().map(|n| self.topsort_ind[n]).collect();
        let min_ind = *nodes.first().unwrap();
        let max_ind = *nodes.last().unwrap();
        for ind in min_ind..=max_ind {
            let n = self.topsort_nodes[ind];
            let mut in_inds = {
                let in_neighs = self.graph.input_neighbours(n);
                in_neighs
                    .map(|n| self.topsort_ind[n])
                    .filter(|&ind| ind >= min_ind)
            };
            if nodes.contains(&ind) {
                if in_inds.any(|ind| self.causal.get(ind) == Causal::Future) {
                    // There is a node in the past that is also in the future!
                    return false;
                }
                self.causal.set(ind, Causal::Past);
            } else {
                let ind_causal = match in_inds
                    .any(|ind| nodes.contains(&ind) || self.causal.get(ind) == Causal::Future)
                {
                    true => Causal::Future,
                    false => Causal::Past,
                };
                self.causal.set(ind, ind_causal);
            }
        }
        true
    }

    /// Whether a subgraph is convex.
    ///
    /// A subgraph is convex if there is no path between two nodes of the
    /// subgraph that has an edge outside of the subgraph.
    ///
    /// Equivalently, we check the following two conditions:
    ///  - There is no node that is both in the past and in the future of
    ///    another node of the subgraph (convexity on induced subgraph),
    ///  - There is no edge from an output port to an input port.
    ///
    /// This function requires mutable access to `self` because it uses a
    /// temporary data structure within the object.
    ///
    /// ## Arguments
    ///
    /// - `nodes`: The nodes of the subgraph of `self.graph`,
    /// - `inputs`: The input ports of the subgraph of `self.graph`. These must
    ///   be [`Direction::Incoming`] ports of a node in `nodes`,
    /// - `outputs`: The output ports of the subgraph of `self.graph`. These
    ///   must be [`Direction::Outgoing`] ports of a node in `nodes`.
    ///
    /// Any edge between two nodes of the subgraph that does not have an explicit
    /// input or output port is considered within the subgraph.
    pub fn is_convex(
        &mut self,
        nodes: impl IntoIterator<Item = NodeIndex>,
        inputs: impl IntoIterator<Item = PortIndex>,
        outputs: impl IntoIterator<Item = PortIndex>,
    ) -> bool {
        let pre_outputs: BTreeSet<_> = outputs
            .into_iter()
            .filter_map(|p| Some(self.graph.port_link(p)?.into()))
            .collect();
        if inputs.into_iter().any(|p| pre_outputs.contains(&p)) {
            return false;
        }
        self.is_node_convex(nodes)
    }
}

/// Whether a node is in the past or in the future of a subgraph.
#[derive(Default, Clone, Debug, PartialEq, Eq)]
enum Causal {
    #[default]
    Past,
    Future,
}

/// A memory-efficient substitute for `Vec<Causal>`.
struct CausalVec(BitVec);

impl From<bool> for Causal {
    fn from(b: bool) -> Self {
        match b {
            true => Self::Future,
            false => Self::Past,
        }
    }
}

impl From<Causal> for bool {
    fn from(c: Causal) -> Self {
        match c {
            Causal::Past => false,
            Causal::Future => true,
        }
    }
}

impl CausalVec {
    fn new(len: usize) -> Self {
        Self(bitvec![0; len])
    }

    fn set(&mut self, index: usize, causal: Causal) {
        self.0.set(index, causal.into());
    }

    fn get(&self, index: usize) -> Causal {
        self.0[index].into()
    }
}

#[cfg(test)]
mod tests {
    use crate::{LinkMut, NodeIndex, PortGraph, PortMut, PortView};

    use super::ConvexChecker;

    fn graph() -> (PortGraph, [NodeIndex; 7]) {
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

        (g, [i1, i2, i3, n1, n2, o1, o2])
    }

    #[test]
    fn induced_convexity_test() {
        let (g, [i1, i2, i3, n1, n2, o1, o2]) = graph();
        let mut checker = ConvexChecker::new(&g);

        assert!(checker.is_node_convex([i1, i2, i3]));
        assert!(checker.is_node_convex([i1, n2]));
        assert!(!checker.is_node_convex([i1, n2, o2]));
        assert!(!checker.is_node_convex([i1, n2, o1]));
        assert!(checker.is_node_convex([i1, n2, o1, n1]));
        assert!(checker.is_node_convex([i1, n2, o2, n1]));
        assert!(checker.is_node_convex([i1, i3, n2]));
        assert!(!checker.is_node_convex([i1, i3, o2]));
    }

    #[test]
    fn edge_convexity_test() {
        let (g, [i1, i2, _, n1, n2, _, o2]) = graph();
        let mut checker = ConvexChecker::new(&g);

        assert!(checker.is_convex(
            [i1, n2],
            [g.input(n2, 1).unwrap()],
            [
                g.output(i1, 0).unwrap(),
                g.output(n2, 0).unwrap(),
                g.output(n2, 1).unwrap()
            ]
        ));

        assert!(checker.is_convex(
            [i2, n1, o2],
            [g.input(n1, 0).unwrap(), g.input(o2, 1).unwrap()],
            [g.output(n1, 0).unwrap(),]
        ));

        assert!(!checker.is_convex(
            [i2, n1, o2],
            [
                g.input(n1, 0).unwrap(),
                g.input(o2, 1).unwrap(),
                g.input(o2, 0).unwrap()
            ],
            [g.output(n1, 0).unwrap(), g.output(n1, 1).unwrap()]
        ));
    }

    #[test]
    fn dangling_input() {
        let mut g = PortGraph::new();
        let n = g.add_node(1, 1);
        let mut checker = ConvexChecker::new(&g);
        assert!(checker.is_node_convex([n]));
    }

    #[test]
    fn disconnected_graph() {
        let mut g = PortGraph::new();
        let n = g.add_node(1, 1);
        g.add_node(1, 1);
        let mut checker = ConvexChecker::new(&g);
        assert!(checker.is_node_convex([n]));
    }
}
