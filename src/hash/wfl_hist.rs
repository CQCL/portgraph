use std::{
    collections::BTreeMap,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use crate::{PortGraph, PortView, Weights};

use super::wfl::wfl_hash;

/// Hasher for graphs using the Weisfeiler-Lehman algorithm with histogram
/// aggregation.
#[derive(Debug)]
pub struct HistWFLHash<H> {
    n_hops: usize,
    _hasher: PhantomData<H>,
}

impl<H> Default for HistWFLHash<H> {
    fn default() -> Self {
        Self {
            n_hops: 1,
            _hasher: Default::default(),
        }
    }
}

impl<H> HistWFLHash<H> {
    /// Create a new hasher.
    pub fn new(n_hops: usize) -> Self {
        Self {
            n_hops,
            _hasher: PhantomData,
        }
    }
}

impl<H: Hasher + Default, N: Clone + Hash, P: Clone + Hash> super::GraphHash<N, P>
    for HistWFLHash<H>
{
    /// Hash a graph using the Weisfeiler-Lehman algorithm.
    fn hash(&self, graph: &PortGraph, weights: &Weights<N, P>) -> u64 {
        let mut hist = BTreeMap::<u64, usize>::new();

        let mut cache = BTreeMap::new();
        for n in graph.nodes_iter() {
            let hash = wfl_hash::<H, _, _>(n, graph, weights, self.n_hops, &mut cache);
            *hist.entry(hash).or_default() += 1;
        }
        let mut hasher = H::default();
        hist.hash(&mut hasher);
        hasher.finish()
    }

    fn name(&self) -> String {
        format!("Hist-WFL({} hops)", self.n_hops)
    }
}
