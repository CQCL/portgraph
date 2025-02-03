use criterion::{criterion_group, Criterion};
use itertools::Itertools;
use portgraph::{algorithms::TopoConvexChecker, PortView};
use portgraph::{NodeIndex, PortGraph};

use crate::helpers::*;

// -----------------------------------------------------------------------------
// Benchmark functions
// -----------------------------------------------------------------------------

struct ConvexConstruction {
    graph: PortGraph,
}
impl SizedBenchmark for ConvexConstruction {
    fn name() -> &'static str {
        "initialize_convexity"
    }

    fn setup(size: usize) -> Self {
        let graph = make_two_track_dag(size);
        Self { graph }
    }

    fn run(&self) -> impl Sized {
        TopoConvexChecker::new(&self.graph)
    }
}

/// We benchmark the worst case scenario, where the "subgraph" is the
/// entire graph itself.
struct ConvexFull {
    checker: TopoConvexChecker<PortGraph>,
    nodes: Vec<NodeIndex>,
}
impl SizedBenchmark for ConvexFull {
    fn name() -> &'static str {
        "check_convexity_full"
    }

    fn setup(size: usize) -> Self {
        let graph = make_two_track_dag(size);
        let nodes = graph.nodes_iter().collect_vec();
        let checker = TopoConvexChecker::new(graph);
        Self { checker, nodes }
    }

    fn run(&self) -> impl Sized {
        self.checker.is_node_convex(self.nodes.iter().copied())
    }
}

/// We benchmark the an scenario where the size of the "subgraph" is sub-linear on the size of the graph.
struct ConvexSparse {
    checker: TopoConvexChecker<PortGraph>,
    nodes: Vec<NodeIndex>,
}
impl SizedBenchmark for ConvexSparse {
    fn name() -> &'static str {
        "check_convexity_sparse"
    }

    fn setup(size: usize) -> Self {
        let graph = make_two_track_dag(size);
        let subgraph_size = (size as f64).sqrt().floor() as usize;
        let nodes = graph
            .nodes_iter()
            .step_by(size / subgraph_size)
            .collect_vec();
        let checker = TopoConvexChecker::new(graph);
        Self { checker, nodes }
    }

    fn run(&self) -> impl Sized {
        self.checker.is_node_convex(self.nodes.iter().copied())
    }
}

// -----------------------------------------------------------------------------
// iai_callgrind definitions
// -----------------------------------------------------------------------------

sized_iai_benchmark!(callgrind_convex_construction, ConvexConstruction);
sized_iai_benchmark!(callgrind_convex_full, ConvexFull);
sized_iai_benchmark!(callgrind_convex_sparse, ConvexSparse);

iai_callgrind::library_benchmark_group!(
    name = callgrind_group;
    benchmarks =
        callgrind_convex_construction,
        callgrind_convex_full,
        callgrind_convex_sparse,
);

// -----------------------------------------------------------------------------
// Criterion definitions
// -----------------------------------------------------------------------------

criterion_group! {
    name = criterion_group;
    config = Criterion::default();
    targets =
        ConvexConstruction::criterion,
        ConvexFull::criterion,
        ConvexSparse::criterion,
}
