#![allow(clippy::unit_arg)] // Required for black_box uses

use super::generators::*;

use criterion::{black_box, criterion_group, AxisScale, BenchmarkId, Criterion, PlotConfiguration};
use portgraph::PortGraph;

/// Remove one every five nodes from the graph.
fn remove_every_five(graph: &mut PortGraph) {
    let mut to_remove = Vec::new();
    for (i, v) in graph.nodes_iter().enumerate() {
        if i % 5 == 0 {
            to_remove.push(v);
        }
    }
    for node in to_remove {
        graph.remove_node(node);
    }
}

/// Remove nodes from the graph in an unordered way until it is empty.
fn remove_all_unordered(graph: &mut PortGraph) {
    while graph.node_count() > 5 {
        remove_every_five(graph);
    }
    // Remove all remaining nodes
    while graph.node_count() > 0 {
        graph.remove_node(graph.nodes_iter().next().unwrap());
    }
}

fn bench_make_portgraph(c: &mut Criterion) {
    let mut g = c.benchmark_group("graph creation");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 10_000, 1_000_000] {
        g.bench_with_input(
            BenchmarkId::new("make_line_graph", size),
            &size,
            |b, size| b.iter(|| black_box(make_line_graph(*size))),
        );
    }
    g.finish();
}

fn bench_clone_portgraph(c: &mut Criterion) {
    let mut g = c.benchmark_group("graph cloning");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 10_000, 1_000_000] {
        g.bench_with_input(
            BenchmarkId::new("clone_line_graph", size),
            &size,
            |b, size| {
                let graph = make_line_graph(*size);
                b.iter(|| black_box(graph.clone()))
            },
        );
    }
    g.finish();
}

fn bench_remove_unordered(c: &mut Criterion) {
    let mut g = c.benchmark_group("remove vertices unordered");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [0, 100, 10_000] {
        g.bench_with_input(
            BenchmarkId::new("remove_vertices_unordered", size),
            &size,
            |b, size| {
                let graph = make_two_track_dag(*size);
                b.iter(|| black_box(remove_all_unordered(&mut graph.clone())))
            },
        );
    }
    g.finish();
}

criterion_group! {
    name = portgraph_benches;
    config = Criterion::default();
    targets =
        bench_make_portgraph,
        bench_clone_portgraph,
        bench_remove_unordered,
}
