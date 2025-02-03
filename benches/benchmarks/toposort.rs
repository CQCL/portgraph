#![allow(clippy::unit_arg)] // Required for black_box uses

use criterion::{criterion_group, Criterion};
use portgraph::{algorithms, Direction, NodeIndex, PortGraph};

use crate::helpers::*;

// -----------------------------------------------------------------------------
// Benchmark functions
// -----------------------------------------------------------------------------

struct Toposort {
    graph: PortGraph,
    roots: [NodeIndex; 2],
}
impl SizedBenchmark for Toposort {
    fn name() -> &'static str {
        "toposort"
    }

    fn setup(size: usize) -> Self {
        let graph = make_two_track_dag(size);
        let roots = [0, 1].map(NodeIndex::new);
        Self { graph, roots }
    }

    fn run(&self) -> impl Sized {
        let topo: algorithms::TopoSort<_> =
            algorithms::toposort(&self.graph, self.roots, Direction::Outgoing);
        // Exhaust the iterator
        topo.fold(0, |n, node| n + node.index());
    }
}

struct PetgraphToposort {
    graph: PortGraph,
}
#[cfg(feature = "petgraph")]
impl SizedBenchmark for PetgraphToposort {
    fn name() -> &'static str {
        "toposort"
    }

    fn setup(size: usize) -> Self {
        let graph = make_two_track_dag(size);
        Self { graph }
    }

    fn run(&self) -> impl Sized {
        petgraph::algo::toposort(&self.graph, None).unwrap();
    }
}

// -----------------------------------------------------------------------------
// iai_callgrind definitions
// -----------------------------------------------------------------------------

sized_iai_benchmark!(callgrind_toposort, Toposort);

iai_callgrind::library_benchmark_group!(
    name = callgrind_group;
    benchmarks = callgrind_toposort
);

// -----------------------------------------------------------------------------
// Criterion definitions
// -----------------------------------------------------------------------------

#[cfg(feature = "petgraph")]
criterion_group! {
    name = criterion_group;
    config = Criterion::default();
    targets =
        Toposort::criterion,
        PetgraphToposort::criterion,
}

#[cfg(not(feature = "petgraph"))]
criterion_group! {
    name = criterion_group;
    config = Criterion::default();
    targets =
        Toposort::criterion,
}
