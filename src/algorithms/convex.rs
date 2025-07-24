//! Convexity checking for portgraphs.
//!
//! This is based on a [`ConvexChecker`] object that is expensive to create
//! (linear in the size of the graph), but can be reused to check multiple
//! subgraphs for convexity quickly.
//!
//! There are currently two implementations of the [`ConvexChecker`] trait:
//! - [`TopoConvexChecker`] uses a pre-computed topological node order to speed up
//!   convexity checks. This is a good default choice for most graphs.
//! - [`LineConvexChecker`] uses a pre-computed line partition, i.e. a partition
//!   of the graph into edge disjoint paths. Convexity checks can then be performed
//!   based on the indices of the nodes in the paths. This will be faster than
//!   [`TopoConvexChecker`] for convexity checking of small subgraphs (say, up to
//!   ~100 nodes), in graphs for which most nodes have few incoming and outgoing
//!   ports. Note that initializing the [`LineConvexChecker`] is up to 4x slower
//!   than initializing the [`TopoConvexChecker`], so must be amortized over
//!   many convexity checks.

mod topo_convex_checker;
#[doc(inline)]
pub use topo_convex_checker::TopoConvexChecker;

mod line_convex_checker;
#[doc(inline)]
pub use line_convex_checker::{
    LineConvexChecker, LineIndex, LineInterval, LineIntervals, Position,
};

use crate::{NodeIndex, PortIndex};

/// Pre-computed data for fast subgraph convexity checking on a given graph.
pub trait ConvexChecker {
    /// Returns `true` if the subgraph is convex.
    ///
    /// A subgraph is convex if there is no path between two nodes of the
    /// subgraph that has an edge outside of the subgraph.
    ///
    /// Equivalently, we check the following two conditions:
    ///  - There is no node that is both in the past and in the future of
    ///    another node of the subgraph (convexity on induced subgraph),
    ///  - There is no edge from an output port to an input port.
    ///
    /// ## Arguments
    ///
    /// - `nodes`: The nodes of the subgraph,
    /// - `inputs`: The input ports of the subgraph. These must
    ///   be [`Direction::Incoming`] ports of a node in `nodes`,
    /// - `outputs`: The output ports of the subgraph. These
    ///   must be [`Direction::Outgoing`] ports of a node in `nodes`.
    ///
    /// Any edge between two nodes of the subgraph that does not have an explicit
    /// input or output port is considered within the subgraph.
    fn is_convex(
        &self,
        nodes: impl IntoIterator<Item = NodeIndex>,
        inputs: impl IntoIterator<Item = PortIndex>,
        outputs: impl IntoIterator<Item = PortIndex>,
    ) -> bool;
}

#[cfg(test)]
mod tests {
    use crate::{
        algorithms::convex::ConvexChecker, LinkMut, LinkView, NodeIndex, PortGraph, PortIndex,
        PortMut, PortView,
    };

    use super::{LineConvexChecker, TopoConvexChecker};

    use rstest::rstest;

    /// A useful enum to abstract over the different convex checkers to test.
    #[allow(clippy::large_enum_variant)]
    enum ConvexCheckerVariants<G> {
        Topo(Option<TopoConvexChecker<G>>),
        Line(Option<LineConvexChecker<G>>),
    }

    impl<G> ConvexCheckerVariants<G>
    where
        G: LinkView + Clone,
    {
        fn new_topo() -> Self {
            Self::Topo(None)
        }

        fn new_line() -> Self {
            Self::Line(None)
        }

        fn init(&mut self, g: G) {
            match self {
                Self::Topo(checker) => *checker = Some(TopoConvexChecker::new(g)),
                Self::Line(checker) => *checker = Some(LineConvexChecker::new(g)),
            }
        }

        fn is_node_convex(&self, nodes: impl IntoIterator<Item = NodeIndex>) -> bool {
            match self {
                Self::Topo(checker) => checker.as_ref().expect("init first").is_node_convex(nodes),
                Self::Line(checker) => checker.as_ref().expect("init first").is_node_convex(nodes),
            }
        }
    }

    impl<G> ConvexChecker for ConvexCheckerVariants<G>
    where
        G: LinkView + Clone,
    {
        fn is_convex(
            &self,
            nodes: impl IntoIterator<Item = NodeIndex>,
            inputs: impl IntoIterator<Item = PortIndex>,
            outputs: impl IntoIterator<Item = PortIndex>,
        ) -> bool {
            match self {
                ConvexCheckerVariants::Topo(checker) => checker
                    .as_ref()
                    .expect("init first")
                    .is_convex(nodes, inputs, outputs),
                ConvexCheckerVariants::Line(checker) => checker
                    .as_ref()
                    .expect("init first")
                    .is_convex(nodes, inputs, outputs),
            }
        }
    }

    pub(super) fn graph() -> (PortGraph, [NodeIndex; 7]) {
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

    #[rstest]
    #[case::topo_checker(ConvexCheckerVariants::new_topo())]
    #[case::line_checker(ConvexCheckerVariants::new_line())]
    fn induced_convexity_test(#[case] mut checker: ConvexCheckerVariants<PortGraph>) {
        let (g, [i1, i2, i3, n1, n2, o1, o2]) = graph();
        checker.init(g);

        assert!(checker.is_node_convex([i1, i2, i3]));
        assert!(checker.is_node_convex([i1, n2]));
        assert!(!checker.is_node_convex([i1, n2, o2]));
        assert!(!checker.is_node_convex([i1, n2, o1]));
        assert!(checker.is_node_convex([i1, n2, o1, n1]));
        assert!(checker.is_node_convex([i1, n2, o2, n1]));
        assert!(checker.is_node_convex([i1, i3, n2]));
        assert!(!checker.is_node_convex([i1, i3, o2]));
    }

    #[rstest]
    #[case::topo_checker(ConvexCheckerVariants::new_topo())]
    #[case::line_checker(ConvexCheckerVariants::new_line())]
    fn edge_convexity_test(#[case] mut checker: ConvexCheckerVariants<PortGraph>) {
        let (g, [i1, i2, _, n1, n2, _, o2]) = graph();
        checker.init(g.clone());

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

    #[rstest]
    #[case::topo_checker(ConvexCheckerVariants::new_topo())]
    #[case::line_checker(ConvexCheckerVariants::new_line())]
    fn dangling_input(#[case] mut checker: ConvexCheckerVariants<PortGraph>) {
        let mut g: PortGraph = PortGraph::new();
        let n = g.add_node(1, 1);
        checker.init(g);
        assert!(checker.is_node_convex([n]));
    }

    #[rstest]
    #[case::topo_checker(ConvexCheckerVariants::new_topo())]
    #[case::line_checker(ConvexCheckerVariants::new_line())]
    fn disconnected_graph(#[case] mut checker: ConvexCheckerVariants<PortGraph>) {
        let mut g: PortGraph = PortGraph::new();
        let n = g.add_node(1, 1);
        g.add_node(1, 1);
        checker.init(g);
        assert!(checker.is_node_convex([n]));
    }
}
