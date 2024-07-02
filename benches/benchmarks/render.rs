//! Benchmarks for the graph renderers.

use criterion::{black_box, criterion_group, AxisScale, BenchmarkId, Criterion, PlotConfiguration};
use portgraph::render::{DotFormat, MermaidFormat};

use super::generators::{make_hierarchy, make_two_track_dag, make_weights};

fn bench_render_mermaid(c: &mut Criterion) {
    let mut g = c.benchmark_group("Mermaid rendering. Graph with hierarchy.");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        let graph = make_two_track_dag(size);
        let hierarchy = make_hierarchy(&graph);
        let weights = make_weights(&graph);
        g.bench_with_input(BenchmarkId::new("hierarchy", size), &size, |b, _size| {
            b.iter(|| {
                black_box(
                    graph
                        .mermaid_format()
                        .with_hierarchy(&hierarchy)
                        .with_weights(&weights)
                        .finish(),
                )
            })
        });
    }
    g.finish();
}

fn bench_render_dot(c: &mut Criterion) {
    let mut g = c.benchmark_group("Dot rendering. Graph with tree hierarchy.");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        let graph = make_two_track_dag(size);
        let hierarchy = make_hierarchy(&graph);
        let weights = make_weights(&graph);
        g.bench_with_input(BenchmarkId::new("hierarchy", size), &size, |b, _size| {
            b.iter(|| {
                black_box(
                    graph
                        .dot_format()
                        .with_hierarchy(&hierarchy)
                        .with_weights(&weights)
                        .finish(),
                )
            })
        });
    }
    g.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets =
        bench_render_mermaid,
        bench_render_dot,
}
