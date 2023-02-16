use crate::graph::LinkError;
use crate::PortIndex;

use super::graph::{Graph, GraphMut, NodeIndex};
use bitvec::bitvec;
use bitvec::prelude::BitVec;
use std::collections::HashMap;
use std::fmt::Debug;
use std::marker::PhantomData;
use thiserror::Error;

pub trait Substitute<'a, N, P>: GraphMut<'a, N, P> + Sized
where
    N: 'a + Clone,
    P: 'a + Clone,
{
    fn apply_rewrite<Other>(&mut self, rewrite: Rewrite<Other, N, P>) -> Result<(), RewriteError>
    where
        for<'other> Other: Graph<'other, N, P> + Sized;
}

impl<'a, G, N, P> Substitute<'a, N, P> for G
where
    G: GraphMut<'a, N, P>,
    N: 'a + Clone,
    P: 'a + Clone,
{
    fn apply_rewrite<Other>(&mut self, rewrite: Rewrite<Other, N, P>) -> Result<(), RewriteError>
    where
        for<'other> Other: Graph<'other, N, P> + Sized,
    {
        rewrite.apply(self).map(|_| ())
    }
}

#[derive(Debug, Error)]
pub enum RewriteError {
    #[error("boundary size mismatch")]
    BoundarySize,
    #[error("Connect Error")]
    Link(LinkError),
}

/// A subgraph defined as a subset of the nodes in a graph.
#[derive(Debug, Clone)]
pub struct SubgraphRef {
    nodes: BitVec,
}

impl SubgraphRef {
    /// Creates a new subgraph from a bit mask of nodes.
    pub fn new(nodes: BitVec) -> Self {
        Self { nodes }
    }

    /// Creates a new subgraph from a set of node indices.
    /// Optionally, the number of nodes in the graph can be specified to pre-allocate space.
    ///
    /// # Panics
    ///
    /// Panics if the number of nodes is specified and the indices are out of bounds.
    pub fn new_from_indices(
        indices: impl IntoIterator<Item = NodeIndex>,
        num_nodes: Option<usize>,
    ) -> Self {
        let mut nodes = if let Some(capacity) = num_nodes {
            bitvec![0; capacity]
        } else {
            BitVec::new()
        };
        for node in indices {
            if num_nodes.is_none() {
                if nodes.len() <= node.index() {
                    nodes.resize(node.index() + 1, false);
                }
            } else {
                debug_assert!(nodes.len() > node.index());
            }
            nodes.set(node.index(), true);
        }
        Self::new(nodes)
    }

    /// Returns the indices of the nodes in the subgraph.
    pub fn nodes(&self) -> impl Iterator<Item = NodeIndex> + '_ {
        self.nodes
            .iter_ones()
            .map(NodeIndex::new)
    }
}

impl FromIterator<NodeIndex> for SubgraphRef {
    fn from_iter<T: IntoIterator<Item = NodeIndex>>(iter: T) -> Self {
        Self::new_from_indices(iter, None)
    }
}

/// A subgraph defined as a subset of the nodes in a graph, and the ports outside of it that are connected to the subgraph.
#[derive(Debug, Clone)]
pub struct BoundedSubgraph {
    pub subgraph: SubgraphRef,
    pub incoming: Vec<PortIndex>,
    pub outgoing: Vec<PortIndex>,
}

impl BoundedSubgraph {
    /// Creates a new bounded subgraph from a subgraph and a set of ports.
    pub fn new(subgraph: SubgraphRef, incoming: Vec<PortIndex>, outgoing: Vec<PortIndex>) -> Self {
        Self {
            subgraph,
            incoming,
            outgoing,
        }
    }

    /// Creates a single-node bounded subgraph.
    pub fn from_node<'a, N, P>(graph: &impl Graph<'a, N, P>, node: NodeIndex) -> Self
    where
        N: 'a + Clone,
        P: 'a + Clone,
    {
        Self {
            subgraph: [node].into_iter().collect(),
            incoming: graph
                .input_links(node)
                .iter()
                .filter_map(|link| *link)
                .collect(),
            outgoing: graph
                .output_links(node)
                .iter()
                .filter_map(|link| *link)
                .collect(),
        }
    }

    /// Returns the indices of the nodes in the subgraph.
    pub fn nodes(&self) -> impl Iterator<Item = NodeIndex> + '_ {
        self.subgraph.nodes()
    }

    /// Checks if the subgraph is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes().next().is_none()
    }

    /// Remove this subgraph from `graph` and return weights of the nodes.
    fn remove_from<'a, G, N, P>(&self, graph: &mut G) -> Vec<Option<N>>
    where
        G: GraphMut<'a, N, P>,
        N: 'a + Clone,
        P: 'a + Clone,
    {
        self.subgraph
            .nodes()
            .map(|n| graph.remove_node(n))
            .collect()
    }
}

/// A graph with explicit input and output ports.
#[derive(Clone)]
pub struct OpenGraph<G, N, P> {
    pub graph: G,
    pub dangling_inputs: Vec<PortIndex>,
    pub dangling_outputs: Vec<PortIndex>,
    phantom: PhantomData<(N, P)>,
}

impl<G, N, P> OpenGraph<G, N, P>
where
    for<'a> G: Graph<'a, N, P>,
    N: Clone,
    P: Clone,
{
    pub fn new(
        graph: G,
        dangling_inputs: Vec<PortIndex>,
        dangling_outputs: Vec<PortIndex>,
    ) -> Self {
        Self {
            graph,
            dangling_inputs,
            dangling_outputs,
            phantom: PhantomData,
        }
    }
}

impl<G: Debug, N, P> Debug for OpenGraph<G, N, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OpenGraph")
            .field("graph", &self.graph)
            .field("in_edges", &self.dangling_inputs)
            .field("out_edges", &self.dangling_outputs)
            .finish()
    }
}

/// A rewrite operation that replaces a subgraph with another graph.
#[derive(Debug, Clone)]
pub struct Rewrite<G, N, P> {
    pub subgraph: BoundedSubgraph,
    pub replacement: OpenGraph<G, N, P>,
}

impl<G, N, P> Rewrite<G, N, P>
where
    for<'a> G: Graph<'a, N, P>,
    N: Clone,
    P: Clone,
{
    pub fn new(subgraph: BoundedSubgraph, replacement: OpenGraph<G, N, P>) -> Self {
        Self {
            subgraph,
            replacement,
        }
    }

    /// Replace a subgraph inside `graph` with a new graph.
    /// Returns the weights of the nodes that were removed.
    pub fn apply<'other, Other>(self, graph: &mut Other) -> Result<Vec<Option<N>>, RewriteError>
    where
        Other: GraphMut<'other, N, P> + Sized,
        N: 'other,
        P: 'other,
    {
        // TODO type check.
        if self.subgraph.incoming.len() != self.replacement.dangling_inputs.len()
            || self.subgraph.outgoing.len() != self.replacement.dangling_outputs.len()
        {
            return Err(RewriteError::BoundarySize);
        }

        let removed = self.subgraph.remove_from(graph);

        // insert new graph and update edge references accordingly
        let mut port_map = HashMap::new();
        graph.insert_graph(
            self.replacement.graph,
            |_, _| {},
            |old, new| {
                port_map.insert(old, new);
            },
        );

        for (repl_port, graph_port) in self
            .replacement
            .dangling_inputs
            .iter()
            .zip(self.subgraph.incoming)
        {
            let repl_port = port_map[repl_port];
            graph.unlink_port(graph_port);
            graph
                .link_ports(graph_port, repl_port)
                .map_err(RewriteError::Link)?;
        }

        for (repl_port, graph_port) in self
            .replacement
            .dangling_outputs
            .iter()
            .zip(self.subgraph.outgoing)
        {
            let repl_port = port_map[repl_port];
            graph.unlink_port(graph_port);
            graph
                .link_ports(repl_port, graph_port)
                .map_err(RewriteError::Link)?;
        }

        Ok(removed)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};
    use std::error::Error;

    use crate::substitute::{BoundedSubgraph, OpenGraph, Rewrite};
    use crate::{Graph, GraphMut, NodeIndex, PortGraph};

    #[test]
    #[ignore = "unimplemented methods"]
    fn test_remove_subgraph() -> Result<(), Box<dyn Error>> {
        let mut g = PortGraph::<i8, i8>::with_capacity(3, 2);

        let n0 = g.add_node(0, 0, 2);
        let n1 = g.add_node(1, 1, 1);
        let n2 = g.add_node(2, 2, 0);

        g.link_nodes(n0, 0, n1, 0)?;
        g.link_nodes(n1, 0, n2, 0)?;
        g.link_nodes(n0, 1, n2, 1)?;

        assert_eq!(g.node_count(), 3);
        assert_eq!(g.port_count(), 6);
        assert_eq!(g.edge_count(), 3);

        let p0 = g.output(n0, 0).unwrap();
        let p1 = g.input(n2, 0).unwrap();

        let mut new_g = g.clone();

        let rem_nodes = BoundedSubgraph::new([n1].into_iter().collect(), vec![p0], vec![p1])
            .remove_from(&mut new_g);

        assert_eq!(rem_nodes, vec![Some(1)]);

        let correct_weights: HashMap<NodeIndex, &i8> = HashMap::from_iter([(n0, &0), (n2, &2)]);
        assert_eq!(HashMap::from_iter(new_g.node_weights()), correct_weights);

        assert_eq!(new_g.node_count(), 2);
        assert_eq!(new_g.edge_count(), 1);

        Ok(())
    }

    #[test]
    #[ignore = "unimplemented methods"]
    fn test_insert_graph() -> Result<(), Box<dyn Error>> {
        let mut g = {
            let mut g = PortGraph::<i8, i8>::with_capacity(3, 2);

            let n0 = g.add_node(0, 0, 1);
            let n1 = g.add_node(1, 1, 1);
            let n2 = g.add_node(2, 1, 0);

            g.link_nodes(n0, 0, n1, 0)?;
            g.link_nodes(n1, 0, n2, 0)?;

            g
        };

        let g2 = {
            let mut g2 = PortGraph::<i8, i8>::with_capacity(2, 1);

            let n3 = g2.add_node(3, 0, 1);
            let n4 = g2.add_node(4, 1, 0);

            g2.link_nodes(n3, 0, n4, 0)?;

            g2
        };

        g.insert_graph(g2, |_, _| {}, |_, _| {});

        let correct_weights: HashSet<_> = HashSet::from_iter([0, 1, 2, 3, 4].into_iter());
        assert_eq!(
            HashSet::from_iter(g.node_weights().map(|(_, w)| *w)),
            correct_weights
        );

        assert_eq!(g.node_count(), 5);
        assert_eq!(g.edge_count(), 3);

        Ok(())
    }

    #[test]
    #[ignore = "unimplemented methods"]
    fn test_replace_subgraph() -> Result<(), Box<dyn Error>> {
        let mut g = PortGraph::<i8, i8>::with_capacity(3, 2);

        let n0 = g.add_node(0, 0, 2);
        let n1 = g.add_node(1, 1, 1);
        let n2 = g.add_node(2, 2, 0);

        g.link_nodes(n0, 0, n1, 0)?;
        g.link_nodes(n1, 0, n2, 0)?;

        let p0 = g.output(n0, 0).unwrap();
        let p1 = g.input(n2, 0).unwrap();

        let mut g2 = PortGraph::<i8, i8>::with_capacity(2, 1);
        // node to be inserted
        let n3 = g2.add_node(3, 1, 1);
        let p2 = g2.input(n3, 0).unwrap();
        let p3 = g2.output(n3, 0).unwrap();

        let rewrite = Rewrite::new(
            BoundedSubgraph::new([n1].into_iter().collect(), vec![p0], vec![p1]),
            OpenGraph::new(g2, vec![p2], vec![p3]),
        );

        let rem_nodes = rewrite.apply(&mut g)?;

        assert_eq!(rem_nodes, vec![Some(1)]);

        let correct_weights: HashSet<_> = HashSet::from_iter([0, 2, 3]);
        assert_eq!(
            HashSet::from_iter(g.node_weights().map(|(_, w)| *w)),
            correct_weights
        );

        assert_eq!(g.node_count(), 3);
        assert_eq!(g.edge_count(), 2);

        Ok(())
    }
}
