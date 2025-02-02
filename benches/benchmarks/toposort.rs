#![allow(clippy::unit_arg)] // Required for black_box uses

use criterion::{black_box, criterion_group, AxisScale, BenchmarkId, Criterion, PlotConfiguration};
use portgraph::{algorithms, Direction, NodeIndex};

use super::generators::*;

// -----------------------------------------------------------------------------
// Benchmark functions
// -----------------------------------------------------------------------------

fn toposort(size: usize) -> impl FnMut() {
    let graph = make_two_track_dag(size);
    let roots = [0, 1].map(NodeIndex::new);
    move || {
        let topo: algorithms::TopoSort<_> =
            algorithms::toposort(&graph, roots, Direction::Outgoing);
        for n in topo {
            black_box(n);
        }
    }
}

#[cfg(feature = "petgraph")]
fn petgraph_toposort(size: usize) -> impl FnMut() {
    let graph = make_two_track_dag(size);
    move || {
        let topo: Vec<_> = petgraph::algo::toposort(&graph, None).unwrap();
        for n in topo {
            black_box(n);
        }
    }
}

// -----------------------------------------------------------------------------
// iai_callgrind definitions
// -----------------------------------------------------------------------------

#[iai_callgrind::library_benchmark]
#[bench::small(toposort(100))]
#[bench::big(toposort(10_000))]
fn callgrind_toposort(mut f: impl FnMut()) {
    f()
}

iai_callgrind::library_benchmark_group!(
    name = callgrind_group;
    benchmarks = callgrind_toposort
);

// -----------------------------------------------------------------------------
// Criterion definitions
// -----------------------------------------------------------------------------

fn criterion_toposort(c: &mut Criterion) {
    let mut g = c.benchmark_group("run toposort on a graph");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        let mut f = toposort(size);
        g.bench_with_input(BenchmarkId::new("toposort", size), &size, |b, _| {
            b.iter(&mut f)
        });
    }
    g.finish();
}

#[cfg(feature = "petgraph")]
fn criterion_petgraph_toposort(c: &mut Criterion) {
    let mut g = c.benchmark_group("run petgraph's toposort on a graph");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        let mut f = petgraph_toposort(size);
        g.bench_with_input(
            BenchmarkId::new("toposort_petgraph", size),
            &size,
            |b, _| b.iter(&mut f),
        );
    }
    g.finish();
}

#[cfg(feature = "petgraph")]
criterion_group! {
    name = criterion_group;
    config = Criterion::default();
    targets =
        criterion_toposort,
        criterion_petgraph_toposort,
}

#[cfg(not(feature = "petgraph"))]
criterion_group! {
    name = criterion_group;
    config = Criterion::default();
    targets =
        criterion_toposort,
}
