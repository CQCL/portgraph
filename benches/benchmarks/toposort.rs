#![allow(clippy::unit_arg)] // Required for black_box uses

use criterion::{black_box, criterion_group, AxisScale, BenchmarkId, Criterion, PlotConfiguration};
use portgraph::{
    algorithms::{toposort, TopoSort},
    Direction, NodeIndex, PortGraph,
};

use super::generators::*;

fn run_toposort(graph: &PortGraph, roots: impl IntoIterator<Item = NodeIndex>) {
    let topo: TopoSort<_> = toposort(graph, roots, Direction::Outgoing);
    for n in topo {
        black_box(n);
    }
}

#[cfg(feature = "petgraph")]
fn run_petgraph_toposort(graph: &PortGraph) {
    let topo: Vec<_> = petgraph::algo::toposort(&graph, None).unwrap();
    for n in topo {
        black_box(n);
    }
}

fn bench_toposort(c: &mut Criterion) {
    let mut g = c.benchmark_group("run toposort on a graph");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        g.bench_with_input(BenchmarkId::new("toposort", size), &size, |b, size| {
            let graph = make_two_track_dag(*size);
            let roots = [0, 1].map(NodeIndex::new);
            b.iter(|| black_box(run_toposort(&graph, roots)))
        });
    }
    g.finish();
}

#[cfg(feature = "petgraph")]
fn bench_petgraph_toposort(c: &mut Criterion) {
    let mut g = c.benchmark_group("run petgraph's toposort on a graph");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        g.bench_with_input(
            BenchmarkId::new("toposort_petgraph", size),
            &size,
            |b, size| {
                let graph = make_two_track_dag(*size);
                b.iter(|| black_box(run_petgraph_toposort(&graph)))
            },
        );
    }
    g.finish();
}

#[cfg(feature = "petgraph")]
criterion_group! {
    name = benches;
    config = Criterion::default();
    targets =
        bench_toposort,
        bench_petgraph_toposort,
}

#[cfg(not(feature = "petgraph"))]
criterion_group! {
    name = benches;
    config = Criterion::default();
    targets =
        bench_toposort,
}
