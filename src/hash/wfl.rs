use std::{
    collections::BTreeMap,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use crate::{LinkView, NodeIndex, PortGraph, PortView, Weights};

/// Hasher for graphs using the Weisfeiler-Lehman algorithm.
#[derive(Debug)]
pub struct WeisfeilerLehmanHash<H> {
    n_hops: usize,
    _hasher: PhantomData<H>,
}

impl<H> Default for WeisfeilerLehmanHash<H> {
    fn default() -> Self {
        Self {
            n_hops: 1,
            _hasher: Default::default(),
        }
    }
}

impl<H> WeisfeilerLehmanHash<H> {
    /// Create a new hasher.
    pub fn new(n_hops: usize) -> Self {
        Self {
            n_hops,
            _hasher: PhantomData,
        }
    }
}

impl<H: Hasher + Default, N: Clone + Hash, P: Clone + Hash> super::GraphHash<N, P>
    for WeisfeilerLehmanHash<H>
{
    /// Hash a graph using the Weisfeiler-Lehman algorithm.
    fn hash(&self, graph: &PortGraph, weights: &Weights<N, P>) -> u64 {
        let mut hash_xor = 0;

        let mut cache = BTreeMap::new();
        for n in graph.nodes_iter() {
            hash_xor = hash_xor ^ wfl_hash::<H, _, _>(n, graph, weights, self.n_hops, &mut cache);
        }
        hash_xor
    }

    fn name(&self) -> String {
        format!("WFL({} hops)", self.n_hops)
    }
}

pub(super) fn wfl_hash<H: Default + Hasher, N: Clone + Hash, P: Clone + Hash>(
    node: NodeIndex,
    graph: &PortGraph,
    weights: &Weights<N, P>,
    hop: usize,
    cache: &mut BTreeMap<(NodeIndex, usize), u64>,
) -> u64 {
    if let Some(res) = cache.get(&(node, hop)) {
        return *res;
    }

    let mut hasher = H::default();

    if hop == 0 {
        let node_data = &weights[node];
        node_data.hash(&mut hasher);
        let res = hasher.finish();
        cache.insert((node, hop), res);
        return res;
    }

    // Hash neighbor labels
    for (this_port, other_port) in graph.all_links(node) {
        let other_node = graph.port_node(other_port).unwrap();
        let other_hash = wfl_hash::<H, _, _>(other_node, graph, weights, hop - 1, cache);
        let this_port_data = &weights[this_port];
        let other_port_data = &weights[other_port];
        let edge_data = (
            other_hash,
            graph.port_offset(this_port).unwrap(),
            this_port_data,
            graph.port_offset(other_port).unwrap(),
            other_port_data,
        );
        edge_data.hash(&mut hasher);
    }

    let res = hasher.finish();
    cache.insert((node, hop), res);
    res
}
