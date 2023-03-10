//! Substitution and rewriting of graphs.
//!
//! This module provides the [`Rewrite`] and [`WeightedRewrite`] types which can
//! be used to define and perform substitutions and rewrites on graphs.
//!
//! TODO: Rewriting with hierarchy. There's some design work to do here with
//! matching the replaced subgraph hierarchy in the replacement.

use crate::portgraph::LinkError;
use crate::weights::Weights;
use crate::{NodeIndex, PortGraph, PortIndex};

use bitvec::bitvec;
use bitvec::prelude::BitVec;
use std::collections::HashMap;
use std::fmt::Debug;
use thiserror::Error;

impl PortGraph {
    /// Applies a rewrite to the graph.
    pub fn apply_rewrite(&mut self, rewrite: Rewrite) -> Result<(), RewriteError> {
        rewrite.apply(self)
    }

    /// Applies a rewrite to the graph and associated weights.
    pub fn apply_weighted_rewrite<N: Clone, P: Clone>(
        &mut self,
        rewrite: WeightedRewrite<N, P>,
        weights: &mut Weights<N, P>,
    ) -> Result<(), RewriteError> {
        rewrite.apply(self, weights)
    }

    /// Applies a rewrite to the graph, calling the provided callbacks as the
    /// rewrite is applied.
    ///
    /// # Parameters
    ///
    /// - `rewrite`: The rewrite to apply.
    /// - `node_removed`: A callback that is called with the index of each node
    ///   that is removed.
    /// - `port_removed`: A callback that is called with the index of each port
    ///   that is removed.
    /// - `node_inserted`: A callback that is called with the old node index in
    ///   the rewrite's [OpenGraph], and the new node index in the graph.
    /// - `port_inserted`: A callback that is called with the old port index in
    ///   the rewrite's [OpenGraph], and the new port index in the graph.
    /// - `ports_connected`: A callback that is called when two ports are connected.
    pub fn apply_rewrite_with_callbacks(
        &mut self,
        rewrite: Rewrite,
        node_removed: impl FnMut(NodeIndex),
        port_removed: impl FnMut(PortIndex),
        node_inserted: impl FnMut(NodeIndex, NodeIndex),
        port_inserted: impl FnMut(PortIndex, PortIndex),
        ports_connected: impl FnMut(PortIndex, PortIndex),
    ) -> Result<(), RewriteError> {
        rewrite.apply_with_callbacks(
            self,
            node_removed,
            port_removed,
            node_inserted,
            port_inserted,
            ports_connected,
        )
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
#[derive(Debug, Clone, Default)]
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
        self.nodes.iter_ones().map(NodeIndex::new)
    }
}

impl FromIterator<NodeIndex> for SubgraphRef {
    fn from_iter<T: IntoIterator<Item = NodeIndex>>(iter: T) -> Self {
        Self::new_from_indices(iter, None)
    }
}

/// A subset of the nodes in a graph, and the ports that it is connected to.
#[derive(Debug, Clone, Default)]
pub struct BoundedSubgraph {
    /// Nodes in the subgraph.
    pub subgraph: SubgraphRef,
    /// [`crate::Direction::Outgoing`] ports outside the subset that are connected to the subgraph.
    pub inputs: Vec<PortIndex>,
    /// [`crate::Direction::Incoming`] ports outside the subset that the subgraph is connected to.
    pub outputs: Vec<PortIndex>,
}

impl BoundedSubgraph {
    /// Creates a new bounded subgraph from a subgraph and a set of ports.
    pub fn new(subgraph: SubgraphRef, incoming: Vec<PortIndex>, outgoing: Vec<PortIndex>) -> Self {
        Self {
            subgraph,
            inputs: incoming,
            outputs: outgoing,
        }
    }

    /// Creates a single-node bounded subgraph.
    pub fn from_node(graph: &PortGraph, node: NodeIndex) -> Self {
        Self {
            subgraph: [node].into_iter().collect(),
            inputs: graph.input_links(node).flatten().collect(),
            outputs: graph.output_links(node).flatten().collect(),
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
    fn remove_from(&self, graph: &mut PortGraph) {
        self.subgraph.nodes().for_each(|n| graph.remove_node(n));
    }
}

/// A graph with explicit input and output ports.
#[derive(Clone, Default)]
pub struct OpenGraph {
    /// The graph.
    pub graph: PortGraph,
    /// [`crate::Direction::Incoming`] dangling ports in the graph.
    pub dangling_inputs: Vec<PortIndex>,
    /// [`crate::Direction::Outgoing`] dangling ports in the graph.
    pub dangling_outputs: Vec<PortIndex>,
}

impl OpenGraph {
    pub fn new(
        graph: PortGraph,
        dangling_inputs: Vec<PortIndex>,
        dangling_outputs: Vec<PortIndex>,
    ) -> Self {
        Self {
            graph,
            dangling_inputs,
            dangling_outputs,
        }
    }
}

impl Debug for OpenGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OpenGraph")
            .field("graph", &self.graph)
            .field("in_edges", &self.dangling_inputs)
            .field("out_edges", &self.dangling_outputs)
            .finish()
    }
}

/// A rewrite operation that replaces a subgraph with another graph.
/// Includes the new weights for the nodes in the replacement graph.
#[derive(Debug, Clone)]
pub struct WeightedRewrite<N = (), P = ()> {
    rewrite: Rewrite,
    replacement_weights: Weights<N, P>,
}

impl<N, P> WeightedRewrite<N, P>
where
    N: Clone,
    P: Clone,
{
    /// Creates a new rewrite operation.
    pub fn new(
        subgraph: BoundedSubgraph,
        replacement: OpenGraph,
        replacement_weights: Weights<N, P>,
    ) -> Self {
        Self {
            rewrite: Rewrite::new(subgraph, replacement),
            replacement_weights,
        }
    }

    /// Applies the rewrite to a graph.
    pub fn apply(
        mut self,
        graph: &mut PortGraph,
        weights: &mut Weights<N, P>,
    ) -> Result<(), RewriteError> {
        let node_inserted = |old, new| {
            std::mem::swap(
                &mut weights.nodes[new],
                &mut self.replacement_weights.nodes[old],
            );
        };
        let port_inserted = |old, new| {
            std::mem::swap(
                &mut weights.ports[new],
                &mut self.replacement_weights.ports[old],
            );
        };
        self.rewrite.apply_with_callbacks(
            graph,
            |_| {},
            |_| {},
            node_inserted,
            port_inserted,
            |_, _| {},
        )
    }
}

/// A rewrite operation that replaces a subgraph with another graph.
#[derive(Debug, Clone, Default)]
pub struct Rewrite {
    pub subgraph: BoundedSubgraph,
    pub replacement: OpenGraph,
}

impl Rewrite {
    /// Creates a new rewrite operation.
    pub fn new(subgraph: BoundedSubgraph, replacement: OpenGraph) -> Self {
        Self {
            subgraph,
            replacement,
        }
    }

    /// Applies the rewrite to a graph.
    pub fn apply(self, graph: &mut PortGraph) -> Result<(), RewriteError> {
        self.apply_with_callbacks(graph, |_| {}, |_| {}, |_, _| {}, |_, _| {}, |_, _| {})
    }

    /// Applies the rewrite to a graph, calling the provided callbacks as the
    /// rewrite is applied.
    ///
    /// # Parameters
    ///
    /// - `graph`: The graph to rewrite.
    /// - `node_removed`: A callback that is called with the index of each node
    ///   that is removed.
    /// - `port_removed`: A callback that is called with the index of each port
    ///   that is removed.
    /// - `node_inserted`: A callback that is called with the old node index in
    ///   the rewrite's [OpenGraph], and the new node index in the graph.
    /// - `port_inserted`: A callback that is called with the old port index in
    ///   the rewrite's [OpenGraph], and the new port index in the graph.
    /// - `ports_connected`: A callback that is called when two ports are
    ///   connected.
    pub fn apply_with_callbacks(
        self,
        graph: &mut PortGraph,
        node_removed: impl FnMut(NodeIndex),
        port_removed: impl FnMut(PortIndex),
        mut node_inserted: impl FnMut(NodeIndex, NodeIndex),
        mut port_inserted: impl FnMut(PortIndex, PortIndex),
        mut ports_connected: impl FnMut(PortIndex, PortIndex),
    ) -> Result<(), RewriteError> {
        // Check that the subgraph and replacement have the same number of dangling ports.
        if self.subgraph.inputs.len() != self.replacement.dangling_inputs.len()
            || self.subgraph.outputs.len() != self.replacement.dangling_outputs.len()
        {
            return Err(RewriteError::BoundarySize);
        }

        // Remove the old nodes, calling the callbacks.
        self.subgraph
            .inputs
            .iter()
            .chain(self.subgraph.outputs.iter())
            .filter_map(|port| graph.port_link(*port))
            .for_each(port_removed);
        self.subgraph.nodes().for_each(node_removed);
        self.subgraph.remove_from(graph);

        // Insert the new graph.
        let node_count = self.replacement.graph.node_count();
        let port_count = self.replacement.graph.port_count();
        let mut port_map = HashMap::with_capacity(port_count);
        graph.reserve(node_count, port_count);
        for node in self.replacement.graph.nodes_iter() {
            let inputs = self.replacement.graph.inputs(node);
            let outputs = self.replacement.graph.outputs(node);
            let new_node = graph.add_node(inputs.len(), outputs.len());

            // Trigger the callbacks and update the port map.
            node_inserted(node, new_node);
            inputs
                .zip(graph.inputs(new_node))
                .for_each(|(old_port, new_port)| {
                    port_inserted(old_port, new_port);
                    port_map.insert(old_port, new_port);
                });
            outputs
                .zip(graph.outputs(new_node))
                .for_each(|(old_port, new_port)| {
                    port_inserted(old_port, new_port);
                    port_map.insert(old_port, new_port);
                });
        }

        // Connect the inserted nodes to the old subgraph boundary.
        let input_links = self.subgraph.inputs.into_iter().zip(
            self.replacement
                .dangling_inputs
                .iter()
                .map(|port| port_map[port]),
        );
        let output_links = self
            .replacement
            .dangling_outputs
            .iter()
            .map(|port| port_map[port])
            .zip(self.subgraph.outputs);
        for (from, to) in input_links.chain(output_links) {
            graph.link_ports(from, to).map_err(RewriteError::Link)?;
            ports_connected(from, to);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::error::Error;

    use crate::substitute::{BoundedSubgraph, OpenGraph, Rewrite, WeightedRewrite};
    use crate::{PortGraph, Weights};

    #[test]
    fn test_remove_subgraph() -> Result<(), Box<dyn Error>> {
        let mut g = PortGraph::with_capacity(3, 2);

        let n0 = g.add_node(0, 2);
        let n1 = g.add_node(1, 1);
        let n2 = g.add_node(2, 0);

        g.link_nodes(n0, 0, n1, 0)?;
        g.link_nodes(n1, 0, n2, 0)?;
        g.link_nodes(n0, 1, n2, 1)?;

        assert_eq!(g.node_count(), 3);
        assert_eq!(g.port_count(), 6);
        assert_eq!(g.link_count(), 3);

        let p0 = g.output(n0, 0).unwrap();
        let p1 = g.input(n2, 0).unwrap();

        let mut new_g = g.clone();

        BoundedSubgraph::new([n1].into_iter().collect(), vec![p0], vec![p1])
            .remove_from(&mut new_g);

        assert_eq!(new_g.node_count(), 2);
        assert_eq!(new_g.link_count(), 1);
        assert!(new_g.connected(n0, n2));

        Ok(())
    }

    #[test]
    fn test_replace_subgraph() -> Result<(), Box<dyn Error>> {
        let mut g = PortGraph::with_capacity(3, 2);

        let n0 = g.add_node(0, 2);
        let n1 = g.add_node(1, 1);
        let n2 = g.add_node(2, 0);

        g.link_nodes(n0, 0, n1, 0)?;
        g.link_nodes(n1, 0, n2, 0)?;

        let _p0 = g.output(n0, 0).unwrap();
        let _p1 = g.input(n2, 0).unwrap();

        let mut g2 = PortGraph::with_capacity(2, 1);
        // node to be inserted
        let n3 = g2.add_node(1, 1);
        let p2 = g2.input(n3, 0).unwrap();
        let p3 = g2.output(n3, 0).unwrap();

        // Replace n1 with n3
        let rewrite = Rewrite::new(
            BoundedSubgraph::from_node(&g, n1),
            OpenGraph::new(g2, vec![p2], vec![p3]),
        );

        rewrite.apply(&mut g)?;

        assert_eq!(g.node_count(), 3);
        assert_eq!(g.link_count(), 2);
        assert!(!g.connected(n0, n2));

        Ok(())
    }

    #[test]
    fn test_replace_subgraph_weighted() -> Result<(), Box<dyn Error>> {
        let mut g = PortGraph::with_capacity(3, 2);
        let mut w = Weights::<i8, i8>::with_capacity(3, 2);

        let n0 = g.add_node(0, 2);
        let n1 = g.add_node(1, 1);
        let n2 = g.add_node(2, 0);
        w[n0] = 0;
        w[n1] = 1;
        w[n2] = 2;

        g.link_nodes(n0, 0, n1, 0)?;
        g.link_nodes(n1, 0, n2, 0)?;

        let _p0 = g.output(n0, 0).unwrap();
        let _p1 = g.input(n2, 0).unwrap();

        let mut g2 = PortGraph::with_capacity(2, 1);
        let mut w2 = Weights::<i8, i8>::with_capacity(2, 1);
        // node to be inserted
        let n3 = g2.add_node(1, 1);
        let p2 = g2.input(n3, 0).unwrap();
        let p3 = g2.output(n3, 0).unwrap();
        w2[n3] = 3;

        // Replace n1 with n3
        let rewrite = WeightedRewrite::new(
            BoundedSubgraph::from_node(&g, n1),
            OpenGraph::new(g2, vec![p2], vec![p3]),
            w2,
        );

        rewrite.apply(&mut g, &mut w)?;

        let correct_weights: HashSet<_> = HashSet::from_iter([0, 2, 3]);
        assert_eq!(
            HashSet::from_iter(g.nodes_iter().map(|n| w[n])),
            correct_weights
        );

        assert_eq!(g.node_count(), 3);
        assert_eq!(g.link_count(), 2);

        Ok(())
    }

    #[test]
    fn test_replace_empty_subgraph() -> Result<(), Box<dyn Error>> {
        let mut g = PortGraph::with_capacity(3, 2);

        let n0 = g.add_node(0, 2);
        let n1 = g.add_node(1, 1);
        let n2 = g.add_node(2, 0);

        g.link_nodes(n0, 0, n1, 0)?;
        g.link_nodes(n1, 0, n2, 0)?;

        // Run an empty rewrite
        let rewrite = Rewrite::new(BoundedSubgraph::default(), OpenGraph::default());

        rewrite.apply(&mut g)?;

        assert_eq!(g.node_count(), 3);
        assert_eq!(g.link_count(), 2);
        assert!(!g.connected(n0, n2));

        Ok(())
    }
}
