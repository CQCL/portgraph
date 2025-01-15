use std::{
    collections::{BTreeMap, BTreeSet},
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use crate::{
    algorithms::{toposort, TopoSort},
    Direction, LinkView, PortGraph, PortView, Weights,
};

/// Hasher for acyclic graphs.
#[derive(Debug, Default)]
pub struct AcyclicHash<H> {
    _hasher: PhantomData<H>,
}

impl<H> AcyclicHash<H> {
    /// Create a new hasher.
    pub fn new() -> Self {
        Self {
            _hasher: PhantomData,
        }
    }
}

impl<H: Default + Hasher, N: Clone + Hash, P: Clone + Hash> super::GraphHash<N, P>
    for AcyclicHash<H>
{
    /// Hash a graph.
    fn hash(&self, graph: &PortGraph, weights: &Weights<N, P>) -> u64 {
        let mut all_hashes = BTreeMap::new();
        let sources = graph
            .nodes_iter()
            .filter(|&n| graph.input_links(n).count() == 0);
        let toposort: TopoSort<_> = toposort(graph, sources, Direction::Outgoing);
        let mut out_hashes = BTreeSet::new();
        for n in toposort {
            let mut hasher = H::default();
            for (in_port, out_port) in graph.input_links(n) {
                let prev_node = graph.port_node(out_port).unwrap();
                let prev_node_hash = all_hashes[&prev_node];
                let in_port_data = &weights[in_port];
                let out_port_data = &weights[out_port];
                let edge_data = (
                    prev_node_hash,
                    graph.port_offset(out_port).unwrap(),
                    out_port_data,
                    graph.port_offset(in_port).unwrap(),
                    in_port_data,
                );
                edge_data.hash(&mut hasher);
            }
            let node_data = &weights[n];
            node_data.hash(&mut hasher);

            let node_hash = hasher.finish();
            all_hashes.insert(n, node_hash);

            if graph.output_links(n).count() == 0 {
                out_hashes.insert(node_hash);
            }
        }

        let mut out_hasher = H::default();
        out_hashes.hash(&mut out_hasher);
        out_hasher.finish()
    }

    fn name(&self) -> String {
        "AcyclicHash".to_string()
    }
}

#[cfg(test)]
mod tests {
    use crate::{LinkMut, PortMut};

    use super::*;
    use std::hash::DefaultHasher;

    #[test]
    fn test_different_graph_hashes() {
        let mut graph1 = PortGraph::new();
        let mut graph2 = PortGraph::new();

        let n1 = graph1.add_node(1, 1);
        let n2 = graph1.add_node(1, 1);
        graph1.link_nodes(n1, 0, n2, 0).unwrap();

        let n3 = graph2.add_node(1, 1);
        let n4 = graph2.add_node(1, 1);
        let n5 = graph2.add_node(1, 1);
        graph2.link_nodes(n3, 0, n4, 0).unwrap();
        graph2.link_nodes(n4, 0, n5, 0).unwrap();

        let empty_weights = |graph: &PortGraph| {
            Weights::<(), ()>::with_capacity(graph.node_capacity(), graph.port_capacity())
        };
        let hasher = AcyclicHash::<DefaultHasher>::new();

        let hash1 = hasher.hash(&graph1, &empty_weights(&graph1));
        let hash2 = hasher.hash(&graph2, &empty_weights(&graph2));

        assert_ne!(
            hash1, hash2,
            "Hashes should be different for different graphs"
        );
    }
}
