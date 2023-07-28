use criterion::{black_box, criterion_group, AxisScale, BenchmarkId, Criterion, PlotConfiguration};
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
fn bench_convex(c: &mut Criterion) {
    let mut g = c.benchmark_group("Runtime convexity check");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        let graph = make_two_track_dag(size);
        let mut checker = ConvexChecker::new(&graph);
        g.bench_with_input(
            BenchmarkId::new("check_convexity", size),
            &size,
            |b, _size| b.iter(|| black_box(checker.is_node_convex(graph.nodes_iter()))),
        );
    }
    g.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets =
        bench_convex,
        bench_convex_construction
}
