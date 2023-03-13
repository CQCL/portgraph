use std::iter::FusedIterator;

use bitvec::vec::BitVec;

use crate::{Direction, NodeIndex, PortGraph};

/// Returns an iterator doing a post-order traversal of a spanning tree in a
/// [`PortGraph`].
///
/// The iterator will visit all nodes reachable from the `source`s, returning
/// the nodes in each subtree following the port order before returning the
/// root.
///
/// # Example
///
/// We create the following tree:
///
/// a ━▸ b ┳━▸ c
///        ┣━▸ d ━▸ e
///        ┗━▸ f
///
/// And traverse it in post-order:
///
/// ```
/// # use portgraph::{algorithms::postorder, Direction, PortGraph};
/// let mut graph = PortGraph::new();
///
/// let a = graph.add_node(0, 1);
/// let b = graph.add_node(1, 3);
/// let c = graph.add_node(1, 1);
/// let d = graph.add_node(1, 1);
/// let e = graph.add_node(1, 0);
/// let f = graph.add_node(1, 0);
///
/// graph.link_nodes(a, 0, b, 0).unwrap();
/// graph.link_nodes(b, 0, c, 0).unwrap();
/// graph.link_nodes(b, 1, d, 0).unwrap();
/// graph.link_nodes(b, 2, f, 0).unwrap();
/// graph.link_nodes(d, 0, e, 0).unwrap();
///
/// // Forward starting from `a`
/// let order = postorder(&graph, vec![a], Direction::Outgoing).collect::<Vec<_>>();
/// assert_eq!(order, vec![c, e, d, f, b, a]);
///
/// // Reverse starting from `e`
/// let order = postorder(&graph, vec![e], Direction::Incoming).collect::<Vec<_>>();
/// assert_eq!(order, vec![a, b, d, e]);
/// ```
///
///
pub fn postorder(
    graph: &PortGraph,
    source: impl IntoIterator<Item = NodeIndex>,
    direction: Direction,
) -> PostOrder {
    PostOrder::new(graph, source, direction)
}

/// Iterator over a [`PortGraph`] in post-order.
///
/// See [`postorder`] for more information.
pub struct PostOrder<'graph> {
    graph: &'graph PortGraph,
    stack: Vec<NodeIndex>,
    visited: BitVec,
    finished: BitVec,
    direction: Direction,
}

impl<'graph> PostOrder<'graph> {
    fn new(
        graph: &'graph PortGraph,
        source: impl IntoIterator<Item = NodeIndex>,
        direction: Direction,
    ) -> Self {
        let mut visited = BitVec::with_capacity(graph.node_capacity());
        visited.resize(graph.node_capacity(), false);
        let mut finished = BitVec::with_capacity(graph.node_capacity());
        finished.resize(graph.node_capacity(), false);

        let mut source: Vec<_> = source.into_iter().collect();
        source.reverse();

        Self {
            graph,
            stack: source,
            visited,
            finished,
            direction,
        }
    }
}

impl<'graph> Iterator for PostOrder<'graph> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.stack.last().copied() {
            if !self.visited.replace(next.index(), true) {
                // The node is visited for the first time. We leave the node on the stack and push
                // all of its neighbours in the traversal direction.
                for port in self.graph.ports(next, self.direction).rev() {
                    let Some(link) = self.graph.port_link(port) else {
                        continue;
                    };

                    let link_node = self.graph.port_node(link).unwrap();

                    if !self.visited[link_node.index()] {
                        self.stack.push(link_node);
                    }
                }
            } else if !self.finished.replace(next.index(), true) {
                // The node is visited for the second time. We remove it from the stack and return
                // as the next node in the traversal.
                self.stack.pop();
                return Some(next);
            } else {
                // The node has already been visited at least twice, so we ignore it.
                self.stack.pop();
            }
        }

        None
    }
}

impl<'graph> FusedIterator for PostOrder<'graph> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn postorder_tree() {
        let mut graph = PortGraph::new();
        // a ━▸ b ┳━▸ c
        //        ┣━▸
        //        ┣━▸ d ━▸ e
        //        ┗━▸ f
        let a = graph.add_node(0, 1);
        let b = graph.add_node(1, 4);
        let c = graph.add_node(1, 1);
        let d = graph.add_node(1, 1);
        let e = graph.add_node(2, 0);
        let f = graph.add_node(1, 0);

        graph.link_nodes(a, 0, b, 0).unwrap();
        graph.link_nodes(b, 0, c, 0).unwrap();
        graph.link_nodes(b, 2, d, 0).unwrap();
        graph.link_nodes(b, 3, f, 0).unwrap();
        graph.link_nodes(d, 0, e, 1).unwrap();

        // Forward starting from `a`
        let order = postorder(&graph, vec![a], Direction::Outgoing).collect::<Vec<_>>();
        assert_eq!(order, vec![c, e, d, f, b, a]);

        // Skipping `a`, starting from `b`
        let order = postorder(&graph, vec![b], Direction::Outgoing).collect::<Vec<_>>();
        assert_eq!(order, vec![c, e, d, f, b]);

        // Exploring `d` before `b`
        let order = postorder(&graph, vec![d, b], Direction::Outgoing).collect::<Vec<_>>();
        assert_eq!(order, vec![e, d, c, f, b]);

        // Reverse starting from `e`
        let order = postorder(&graph, vec![e], Direction::Incoming).collect::<Vec<_>>();
        assert_eq!(order, vec![a, b, d, e]);
    }

    #[test]
    fn postorder_dag() {
        let mut graph = PortGraph::new();
        // a -> b -> c
        //       \     \
        //        \--------> d
        let a = graph.add_node(0, 1);
        let b = graph.add_node(1, 2);
        let c = graph.add_node(1, 1);
        let d = graph.add_node(2, 0);

        graph.link_nodes(a, 0, b, 0).unwrap();
        graph.link_nodes(b, 0, c, 0).unwrap();
        graph.link_nodes(b, 1, d, 0).unwrap();
        graph.link_nodes(c, 0, d, 1).unwrap();

        // Forward starting from `a`
        let order = postorder(&graph, vec![a], Direction::Outgoing).collect::<Vec<_>>();
        assert_eq!(order, vec![d, c, b, a]);

        // Backwards starting from `d`
        let order = postorder(&graph, vec![d], Direction::Incoming).collect::<Vec<_>>();
        assert_eq!(order, vec![a, b, c, d]);
    }

    #[test]
    fn postorder_cycle() {
        let mut graph = PortGraph::new();
        // a -> b -> c -> d -> b -> ...
        let a = graph.add_node(0, 1);
        let b = graph.add_node(3, 2);
        let c = graph.add_node(1, 1);
        let d = graph.add_node(1, 1);

        graph.link_nodes(a, 0, b, 0).unwrap();
        graph.link_nodes(b, 0, c, 0).unwrap();
        graph.link_nodes(c, 0, d, 0).unwrap();
        graph.link_nodes(d, 0, b, 2).unwrap();

        // Forward starting from `a`
        let order = postorder(&graph, vec![a], Direction::Outgoing).collect::<Vec<_>>();
        assert_eq!(order, vec![d, c, b, a]);

        // Backwards starting from `c`
        let order = postorder(&graph, vec![c], Direction::Incoming).collect::<Vec<_>>();
        assert_eq!(order, vec![a, d, b, c]);
    }
}
