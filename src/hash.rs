use crate::{PortGraph, Weights};

/// A trait for hashing graphs.
pub trait GraphHash<N, P> {
    /// Hash a graph.
    fn hash(&self, graph: &PortGraph, weights: &Weights<N, P>) -> u64;

    /// Get the name of the hasher.
    fn name(&self) -> String;
}

mod acyclic;
pub use acyclic::AcyclicHash;

mod wfl;
pub use wfl::WeisfeilerLehmanHash;

mod wfl_sparse;
pub use wfl_sparse::WeisfeilerLehmanSparseHash;
