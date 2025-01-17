use std::{
    collections::BTreeMap,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use crate::{LinkView, NodeIndex, PortGraph, PortView, Weights};

use super::wfl::wfl_hash;

/// Hasher for graphs using the Weisfeiler-Lehman algorithm.
#[derive(Debug)]
pub struct WeisfeilerLehmanSparseHash<H> {
    n_hops: usize,
    _hasher: PhantomData<H>,
}

impl<H> Default for WeisfeilerLehmanSparseHash<H> {
    fn default() -> Self {
        Self {
            n_hops: 1,
            _hasher: Default::default(),
        }
    }
}

impl<H> WeisfeilerLehmanSparseHash<H> {
    /// Create a new hasher.
    pub fn new(n_hops: usize) -> Self {
        Self {
            n_hops,
            _hasher: PhantomData,
        }
    }
}

/// A label associated with a node for heuristic purposes.
fn node_label<H: Hasher + Default, N: Clone + Hash, P: Clone + Hash>(
    node: NodeIndex,
    graph: &PortGraph,
    weights: &Weights<N, P>,
) -> u64 {
    let mut hasher = H::default();
    weights[node].hash(&mut hasher);
    hasher.finish()
}

fn node_is_sink<H: Hasher + Default, N: Clone + Hash, P: Clone + Hash>(
    node: NodeIndex,
    graph: &PortGraph,
    weights: &Weights<N, P>,
) -> bool {
    let mut all_neigh_vals = graph
        .all_neighbours(node)
        .map(|n| node_label::<H, _, _>(n, graph, weights));
    let self_val = node_label::<H, _, _>(node, graph, weights);
    all_neigh_vals.all(|v| v > self_val)
}

impl<H: Hasher + Default, N: Clone + Hash, P: Clone + Hash> super::GraphHash<N, P>
    for WeisfeilerLehmanSparseHash<H>
{
    /// Hash a graph using the Weisfeiler-Lehman algorithm.
    fn hash(&self, graph: &PortGraph, weights: &Weights<N, P>) -> u64 {
        let mut hash_xor = 0;

        let mut cache = BTreeMap::new();
        // let mut cnt = 0;
        for n in graph
            .nodes_iter()
            .filter(|&n| node_is_sink::<H, _, _>(n, graph, weights))
        {
            hash_xor = hash_xor ^ wfl_hash::<H, _, _>(n, graph, weights, self.n_hops, &mut cache);
            // cnt += 1;
        }
        // println!(
        //     "Hashed {:.2}% of nodes",
        //     100. * (cnt as f64) / graph.node_count() as f64
        // );
        hash_xor
    }

    fn name(&self) -> String {
        format!("Sparse-WFL({} hops)", self.n_hops)
    }
}
