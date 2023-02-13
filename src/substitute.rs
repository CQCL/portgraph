use crate::PortIndex;

use super::graph::{Direction, EdgeIndex, Graph, NodeIndex, PortGraph, DIRECTIONS};
use bitvec::prelude::BitVec;
use std::collections::BTreeSet;
use std::fmt::{Debug, Display};
use thiserror::Error;

#[derive(Debug, Clone)]
pub struct SubgraphRef {
    pub nodes: BitVec,
}

impl SubgraphRef {
    pub fn new(nodes: BitVec) -> Self {
        Self { nodes }
    }
}

impl FromIterator<NodeIndex> for SubgraphRef {
    fn from_iter<T: IntoIterator<Item = NodeIndex>>(iter: T) -> Self {
        let mut nodes = BitVec::new();
        for node in iter {
            if nodes.len() <= node.index() {
                nodes.resize(node.index() + 1, false);
            }
            nodes.set(node.index(), true);
        }
        Self::new(nodes)
    }
}

#[derive(Debug, Clone)]
pub struct BoundedSubgraph {
    pub subgraph: SubgraphRef,
    pub ports: [Vec<PortIndex>; 2],
}

impl BoundedSubgraph {
    pub fn new(subgraph: SubgraphRef, ports: [Vec<PortIndex>; 2]) -> Self {
        Self { subgraph, ports }
    }

    pub fn from_node<N, P>(graph: &PortGraph<N, P>, node: NodeIndex) -> Self
    where
        N: Default,
        P: Default,
    {
        Self {
            subgraph: [node].into_iter().collect(),
            ports: [
                graph.ports(node, Direction::Incoming).collect(),
                graph.ports(node, Direction::Outgoing).collect(),
            ],
        }
    }
}

#[derive(Clone)]
pub struct OpenGraph<N, P> {
    pub graph: PortGraph<N, P>,
    pub dangling: [Vec<EdgeIndex>; 2],
}

impl<N, P> OpenGraph<N, P> {
    pub fn new(
        graph: PortGraph<N, P>,
        in_ports: Vec<EdgeIndex>,
        out_ports: Vec<EdgeIndex>,
    ) -> Self {
        Self {
            graph,
            dangling: [in_ports, out_ports],
        }
    }
}

impl<N: Debug, P: Debug> Debug for OpenGraph<N, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OpenGraph")
            .field("graph", &self.graph)
            .field("in_edges", &self.dangling[0])
            .field("out_edges", &self.dangling[1])
            .finish()
    }
}

#[derive(Debug, Clone)]
pub struct Rewrite<N, P> {
    pub subg: BoundedSubgraph,
    pub replacement: OpenGraph<N, P>,
}

impl<N, P> Rewrite<N, P> {
    pub fn new(subg: BoundedSubgraph, replacement: OpenGraph<N, P>) -> Self {
        Self { subg, replacement }
    }
}

impl<N: Default + Debug + Display, P: Default + Debug + Display> PortGraph<N, P> {
    /// Remove subgraph formed by subg and return weights of nodes inside subg
    #[allow(dead_code)] // TODO remove this
    fn remove_subgraph(&mut self, subgraph: &BoundedSubgraph) -> Vec<Option<N>> {
        let boundary_ports =
            BTreeSet::from_iter(subgraph.ports.iter().flat_map(|x| x.iter().copied()));
        subgraph
            .subgraph
            .nodes
            .iter_ones()
            .map(|n| {
                let n = NodeIndex::new(n);
                let ports: Vec<_> = DIRECTIONS
                    .iter()
                    .flat_map(|d| self.ports(n, *d))
                    .filter(|e| !boundary_ports.contains(e))
                    .collect();

                for port in ports {
                    self.disconnect_port(port);
                }

                self.remove_node(n)
            })
            .collect()
    }

    /* TODO: Implement this for the new graph structure
    fn replace_subgraph(
        &mut self,
        subgraph: BoundedSubgraph,
        replacement: OpenGraph<N, P>,
    ) -> Result<Vec<Option<N>>, RewriteError> {
        if subgraph.subgraph.nodes.is_empty() {
            return Err(RewriteError::EmptySubgraph);
        }

        // TODO type check.
        for direction in DIRECTIONS {
            let subgraph_ports = &subgraph.ports[direction.index()];
            let ports = &replacement.dangling[direction.index()];

            if subgraph_ports.len() != ports.len() {
                return Err(RewriteError::BoundarySize);
            }
        }

        let removed = self.remove_subgraph(&subgraph);

        // insert new graph and update edge references accordingly
        let (_, mut edge_map) = self.insert_graph(replacement.graph);

        for direction in DIRECTIONS {
            let subg_ports = &subgraph.ports[direction.index()];
            let repl_ports = &replacement.dangling[direction.index()];

            for (sub_port, repl_port) in subg_ports.iter().zip(repl_ports) {
                // TODO: There should be a check to make sure this can not fail
                // before we merge the first edge to avoid leaving the graph in an
                // invalid state.
                self.merge_edges(port_map[repl_edge], *sub_port).unwrap();
                // Update edge_map to point to new merged edge
                if let Some(e) = port_map.get_mut(repl_port) {
                    *e = *sub_port;
                }
            }
        }

        Ok(removed)
    }

    pub fn apply_rewrite(&mut self, rewrite: Rewrite<N, P>) -> Result<(), RewriteError> {
        self.replace_subgraph(rewrite.subg, rewrite.replacement)?;
        Ok(())
    }
    */
}

#[derive(Debug, Error)]
pub enum RewriteError {
    #[error("cannot replace empty subgraph")]
    EmptySubgraph,
    #[error("boundary size mismatch")]
    BoundarySize,
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::error::Error;

    use crate::substitute::{BoundedSubgraph, OpenGraph};

    use super::PortGraph;

    #[test]
    fn test_remove_subgraph() -> Result<(), Box<dyn Error>> {
        let mut g = PortGraph::<i8, i8>::with_capacity(3, 2);

        let e1 = g.add_edge(-1);
        let e2 = g.add_edge(-2);
        let e3 = g.add_edge(-3);

        let _ = g.add_node_with_edges(0, [], [e1, e3])?;
        let n1 = g.add_node_with_edges(1, [e1], [e2])?;
        let _ = g.add_node_with_edges(2, [e2, e3], [])?;

        assert_eq!(g.node_count(), 3);
        assert_eq!(g.edge_count(), 3);

        let mut new_g = g.clone();

        let rem_nodes = new_g.remove_subgraph(&BoundedSubgraph::new(
            [n1].into_iter().collect(),
            [vec![e1], vec![e2]],
        ));

        assert_eq!(rem_nodes, vec![Some(1)]);

        let correct_weights: HashSet<_> = HashSet::from_iter([0, 2]);
        assert_eq!(
            HashSet::from_iter(new_g.node_weights().copied()),
            correct_weights
        );

        let correct_weights: HashSet<_> = HashSet::from_iter([-1, -2, -3]);
        assert_eq!(
            HashSet::from_iter(new_g.edge_weights().copied()),
            correct_weights
        );

        assert_eq!(new_g.edge_count(), 3);
        assert_eq!(new_g.node_count(), 2);

        Ok(())
    }

    #[test]
    fn test_insert_graph() -> Result<(), Box<dyn Error>> {
        let mut g = {
            let mut g = PortGraph::<i8, i8>::with_capacity(3, 2);

            let e1 = g.add_edge(-1);
            let e2 = g.add_edge(-2);

            let _ = g.add_node_with_edges(0, [], [e1])?;
            let _ = g.add_node_with_edges(1, [e1], [e2])?;
            let _ = g.add_node_with_edges(2, [e2], [])?;

            g
        };

        let g2 = {
            let mut g2 = PortGraph::<i8, i8>::with_capacity(2, 1);

            let e3 = g2.add_edge(-3);

            let _ = g2.add_node_with_edges(3, [], [e3])?;
            let _ = g2.add_node_with_edges(4, [e3], [])?;

            g2
        };

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

        Ok(())
    }

    #[test]
    fn test_replace_subgraph() -> Result<(), Box<dyn Error>> {
        let mut g = PortGraph::<i8, i8>::with_capacity(3, 2);

        let e1 = g.add_edge(-1);
        let e2 = g.add_edge(-2);
        let e3 = g.add_edge(-3);

        let _ = g.add_node_with_edges(0, [], [e1, e3])?;
        let n1 = g.add_node_with_edges(1, [e1], [e2])?;
        let _ = g.add_node_with_edges(2, [e2, e3], [])?;

        let mut g2 = PortGraph::<i8, i8>::with_capacity(2, 1);
        // node to be inserted
        let e4 = g2.add_edge(-4);
        let e5 = g2.add_edge(-5);
        let _ = g2.add_node_with_edges(3, [e4], [e5])?;

        let rem_nodes = g
            .replace_subgraph(
                BoundedSubgraph::new([n1].into_iter().collect(), [vec![e1], vec![e2]]),
                OpenGraph::new(g2, vec![e4], vec![e5]),
            )
            .unwrap();

        assert_eq!(rem_nodes, vec![Some(1)]);

        let correct_weights: HashSet<_> = HashSet::from_iter([0, 2, 3]);
        assert_eq!(
            HashSet::from_iter(g.node_weights().copied()),
            correct_weights
        );

        let correct_weights: HashSet<_> = HashSet::from_iter([-1, -2, -3]);
        assert_eq!(
            HashSet::from_iter(g.edge_weights().copied()),
            correct_weights
        );

        Ok(())
    }
}
