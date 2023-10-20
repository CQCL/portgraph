use criterion::{black_box, criterion_group, AxisScale, BenchmarkId, Criterion, PlotConfiguration};
use itertools::Itertools;
use portgraph::{algorithms::ConvexChecker, PortView};

use super::generators::make_two_track_dag;

fn bench_convex_construction(c: &mut Criterion) {
    let mut g = c.benchmark_group("initialize convex checker object");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        g.bench_with_input(
            BenchmarkId::new("initalize_convexity", size),
            &size,
            |b, size| {
                let graph = make_two_track_dag(*size);
                b.iter(|| black_box(ConvexChecker::new(&graph)))
            },
        );
    }
    g.finish();
}

/// We benchmark the worst case scenario, where the "subgraph" is the
/// entire graph itself.
fn bench_convex_full(c: &mut Criterion) {
    let mut g = c.benchmark_group("Runtime convexity check. Full graph.");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        let graph = make_two_track_dag(size);
        let checker = ConvexChecker::new(&graph);
        g.bench_with_input(
            BenchmarkId::new("check_convexity_full", size),
            &size,
            |b, _size| b.iter(|| black_box(checker.is_node_convex(graph.nodes_iter()))),
        );
    }
    g.finish();
}

/// We benchmark the an scenario where the size of the "subgraph" is sub-linear on the size of the graph.
fn bench_convex_sparse(c: &mut Criterion) {
    let mut g = c.benchmark_group("Runtime convexity check. Sparse subgraph on an n^2 size graph.");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100usize, 1_000, 5_000] {
        let graph_size = size.pow(2);
        let graph = make_two_track_dag(graph_size);
        let checker = ConvexChecker::new(&graph);
        let nodes = graph.nodes_iter().step_by(graph_size / size).collect_vec();
        g.bench_with_input(
            BenchmarkId::new("check_convexity_sparse", size),
            &size,
            |b, _size| b.iter(|| black_box(checker.is_node_convex(nodes.iter().copied()))),
        );
    }
    g.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets =
        bench_convex_full,
        bench_convex_sparse,
        bench_convex_construction
}
