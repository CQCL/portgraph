use criterion::{criterion_group, Criterion};
use itertools::Itertools;
use portgraph::algorithms::{LineConvexChecker, TopoConvexChecker};
use portgraph::PortView;
use portgraph::{NodeIndex, PortGraph};

use crate::helpers::*;

// -----------------------------------------------------------------------------
// Benchmark functions
// -----------------------------------------------------------------------------

/// Macro to generate convexity benchmark structs and impls for a given checker.
/// The macro takes four arguments:
/// - The checker type (e.g., TopoConvexChecker)
/// - The struct name for construction (e.g., ConvexConstruction)
/// - The struct name for full subgraph (e.g., ConvexFull)
/// - The struct name for sparse subgraph (e.g., ConvexSparse)
#[macro_export]
macro_rules! convex_benchmarks {
    ($checker_ty:ty, $construction:ident, $full:ident, $sparse:ident, $fixed_size:ident) => {
        struct $construction {
            graph: PortGraph,
        }
        impl SizedBenchmarkWithInput for $construction {
            type State = PortGraph;

            fn name() -> &'static str {
                concat!("initialize_convexity_", stringify!($checker_ty))
            }

            fn setup(size: usize) -> Self {
                let graph = make_two_track_dag(size);
                Self { graph }
            }

            fn prepare_run(&self) -> Self::State {
                self.graph.clone()
            }

            fn run(&self, graph: Self::State) -> impl Sized {
                <$checker_ty>::new(graph)
            }
        }

        /// We benchmark the worst case scenario, where the "subgraph" is the
        /// entire graph itself.
        struct $full {
            checker: $checker_ty,
            nodes: Vec<NodeIndex>,
        }
        impl SizedBenchmark for $full {
            fn name() -> &'static str {
                concat!("check_convexity_full_", stringify!($checker_ty))
            }

            fn setup(size: usize) -> Self {
                let graph = make_two_track_dag(size);
                let nodes = graph.nodes_iter().collect_vec();
                let checker = <$checker_ty>::new(graph);
                Self { checker, nodes }
            }

            fn run(&self) -> impl Sized {
                self.checker.is_node_convex(self.nodes.iter().copied())
            }
        }

        /// We benchmark a scenario where the size of the "subgraph" is sub-linear on the size of the graph.
        struct $sparse {
            checker: $checker_ty,
            nodes: Vec<NodeIndex>,
        }
        impl SizedBenchmark for $sparse {
            fn name() -> &'static str {
                concat!("check_convexity_sparse_", stringify!($checker_ty))
            }

            fn setup(size: usize) -> Self {
                let graph = make_two_track_dag(size);
                let subgraph_size = (size as f64).sqrt().floor() as usize;
                let nodes = graph
                    .nodes_iter()
                    .step_by(size / subgraph_size)
                    .collect_vec();
                let checker = <$checker_ty>::new(graph);
                Self { checker, nodes }
            }

            fn run(&self) -> impl Sized {
                self.checker.is_node_convex(self.nodes.iter().copied())
            }
        }

        struct $fixed_size {
            checker: $checker_ty,
            subgraphs: [Vec<NodeIndex>; 3],
        }
        impl SizedBenchmark for $fixed_size {
            fn name() -> &'static str {
                concat!("check_convexity_fixed_size_", stringify!($checker_ty))
            }

            fn setup(size: usize) -> Self {
                let graph = make_square_circuit((size as f64).sqrt().floor() as usize);
                const SUBGRAPH_RADIUS: usize = 2;
                let mut subgraphs = [Vec::new(), Vec::new(), Vec::new()];
                for i in 1..=3 {
                    // create a subgraph centered around the node at 1/4-th, 1/2-th, 3/4-th of the graph
                    let mid_node = graph.nodes_iter().nth(i * graph.node_count() / 4).unwrap();
                    let nodes = within_radius(&graph, mid_node, SUBGRAPH_RADIUS);
                    subgraphs[i - 1] = nodes;
                }
                let checker = <$checker_ty>::new(graph);
                Self { checker, subgraphs }
            }

            fn run(&self) -> impl Sized {
                for subgraph in self.subgraphs.iter() {
                    std::hint::black_box(self.checker.is_node_convex(subgraph.iter().copied()));
                }
            }
        }
    };
}

convex_benchmarks!(
    TopoConvexChecker<PortGraph>,
    ConvexConstructionTopo,
    ConvexFullTopo,
    ConvexSparseTopo,
    ConvexFixedSizeTopo
);

convex_benchmarks!(
    LineConvexChecker<PortGraph>,
    ConvexConstructionLine,
    ConvexFullLine,
    ConvexSparseLine,
    ConvexFixedSizeLine
);

// -----------------------------------------------------------------------------
// iai_callgrind definitions
// -----------------------------------------------------------------------------

sized_iai_benchmark_with_input!(callgrind_convex_construction_topo, ConvexConstructionTopo);
sized_iai_benchmark!(callgrind_convex_full_topo, ConvexFullTopo);
sized_iai_benchmark!(callgrind_convex_sparse_topo, ConvexSparseTopo);
sized_iai_benchmark!(callgrind_convex_fixed_size_topo, ConvexFixedSizeTopo);
sized_iai_benchmark_with_input!(callgrind_convex_construction_line, ConvexConstructionLine);
sized_iai_benchmark!(callgrind_convex_full_line, ConvexFullLine);
sized_iai_benchmark!(callgrind_convex_sparse_line, ConvexSparseLine);
sized_iai_benchmark!(callgrind_convex_fixed_size_line, ConvexFixedSizeLine);

iai_callgrind::library_benchmark_group!(
    name = callgrind_group;
    benchmarks =
        callgrind_convex_construction_topo,
        callgrind_convex_full_topo,
        callgrind_convex_sparse_topo,
        callgrind_convex_fixed_size_topo,
        callgrind_convex_construction_line,
        callgrind_convex_full_line,
        callgrind_convex_sparse_line,
        callgrind_convex_fixed_size_line,
);

// -----------------------------------------------------------------------------
// Criterion definitions
// -----------------------------------------------------------------------------

criterion_group! {
    name = criterion_group;
    config = Criterion::default();
    targets =
        ConvexConstructionTopo::criterion,
        ConvexFullTopo::criterion,
        ConvexSparseTopo::criterion,
        ConvexFixedSizeTopo::criterion,
        ConvexConstructionLine::criterion,
        ConvexFullLine::criterion,
        ConvexSparseLine::criterion,
        ConvexFixedSizeLine::criterion,
}
