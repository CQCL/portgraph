use std::iter::FusedIterator;

use bitvec::vec::BitVec;

use crate::{Direction, NodeIndex, PortGraph};

/// Iterator over an `UnweightedGraph` in post-order.
pub struct PostOrder<'graph> {
    graph: &'graph PortGraph,
    stack: Vec<NodeIndex>,
    visited: BitVec,
    finished: BitVec,
    direction: Direction,
}

impl<'graph> PostOrder<'graph> {
    pub fn new(
        graph: &'graph PortGraph,
        source: impl IntoIterator<Item = NodeIndex>,
        direction: Direction,
    ) -> Self {
        let mut visited = BitVec::with_capacity(graph.node_capacity());
        visited.resize(graph.node_capacity(), false);
        let mut finished = BitVec::with_capacity(graph.node_capacity());
        finished.resize(graph.node_capacity(), false);

        Self {
            graph,
            stack: source.into_iter().collect(),
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
                for port in self.graph.ports(next, self.direction) {
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
