//! Benchmarks for the graph renderers.

use criterion::{black_box, criterion_group, AxisScale, BenchmarkId, Criterion, PlotConfiguration};
use portgraph::render::{DotFormat, MermaidFormat};

use super::generators::{make_hierarchy, make_two_track_dag, make_weights};

// -----------------------------------------------------------------------------
// Benchmark functions
// -----------------------------------------------------------------------------

fn render_mermaid(size: usize) -> impl FnMut() {
    let graph = make_two_track_dag(size);
    let hierarchy = make_hierarchy(&graph);
    let weights = make_weights(&graph);
    move || {
        black_box(
            graph
                .mermaid_format()
                .with_hierarchy(&hierarchy)
                .with_weights(&weights)
                .finish(),
        );
    }
}

fn render_dot(size: usize) -> impl FnMut() {
    let graph = make_two_track_dag(size);
    let hierarchy = make_hierarchy(&graph);
    let weights = make_weights(&graph);
    move || {
        black_box(
            graph
                .dot_format()
                .with_hierarchy(&hierarchy)
                .with_weights(&weights)
                .finish(),
        );
    }
}

// -----------------------------------------------------------------------------
// iai_callgrind definitions
// -----------------------------------------------------------------------------

#[iai_callgrind::library_benchmark]
#[bench::small(render_mermaid(100))]
#[bench::big(render_mermaid(10_000))]
fn callgrind_render_mermaid(mut f: impl FnMut()) {
    f()
}

#[iai_callgrind::library_benchmark]
#[bench::small(render_dot(100))]
#[bench::big(render_dot(10_000))]
fn callgrind_render_dot(mut f: impl FnMut()) {
    f()
}

iai_callgrind::library_benchmark_group!(
    name = callgrind_group;
    benchmarks = callgrind_render_dot, callgrind_render_mermaid
);

// -----------------------------------------------------------------------------
// Criterion definitions
// -----------------------------------------------------------------------------

fn criterion_render_mermaid(c: &mut Criterion) {
    let mut g = c.benchmark_group("Mermaid rendering. Graph with hierarchy.");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        let mut f = render_mermaid(size);
        g.bench_with_input(BenchmarkId::new("hierarchy", size), &size, |b, _size| {
            b.iter(&mut f)
        });
    }
    g.finish();
}

fn criterion_render_dot(c: &mut Criterion) {
    let mut g = c.benchmark_group("Dot rendering. Graph with tree hierarchy.");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        let mut f = render_dot(size);
        g.bench_with_input(BenchmarkId::new("hierarchy", size), &size, |b, _size| {
            b.iter(&mut f)
        });
    }
    g.finish();
}

criterion_group! {
    name = criterion_group;
    config = Criterion::default();
    targets =
        criterion_render_mermaid,
        criterion_render_dot,
}
