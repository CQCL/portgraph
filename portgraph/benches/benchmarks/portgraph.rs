#![allow(clippy::unit_arg)] // Required for black_box uses

use super::generators::*;

use criterion::{
    black_box, criterion_group, AxisScale, BatchSize, BenchmarkId, Criterion, PlotConfiguration,
};
use portgraph::{PortGraph, PortView};

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

/// Adds or removes one port from an arbitrary node, `amount` times.
fn resize_ports(graph: &mut PortGraph, amount: usize) {
    let nodes = graph.nodes_iter().cycle().take(amount).collect::<Vec<_>>();
    for (i, node) in nodes.iter().copied().enumerate() {
        let mut inputs = graph.num_inputs(node);
        let mut outputs = graph.num_outputs(node);

        // Choose the direction to resize, and whether to grow or shrink
        let direction = i % 2 == 0;
        let grow = i % 3 != 0;

        let amount = if direction { &mut outputs } else { &mut inputs };
        if grow || *amount == 0 {
            *amount += 1;
        } else {
            *amount -= 1;
        }
        graph.set_num_ports(node, inputs, outputs, |_, _| {});
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

    for size in [100, 1_000, 10_000] {
        g.bench_with_input(
            BenchmarkId::new("remove_vertices_unordered", size),
            &size,
            |b, size| {
                let graph = make_two_track_dag(*size);
                b.iter_batched(
                    || graph.clone(),
                    |mut graph| black_box(remove_all_unordered(&mut graph)),
                    BatchSize::SmallInput,
                )
            },
        );
    }
    g.finish();
}

fn bench_resize_ports(c: &mut Criterion) {
    let mut g = c.benchmark_group("resize the amount of ports");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        g.bench_with_input(BenchmarkId::new("set_num_ports", size), &size, |b, size| {
            // Small graph so nodes are modified multiple times
            let graph = make_two_track_dag(*size / 4);
            b.iter_batched(
                || graph.clone(),
                |mut graph| black_box(resize_ports(&mut graph, *size)),
                BatchSize::SmallInput,
            )
        });
    }
    g.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets =
        bench_make_portgraph,
        bench_clone_portgraph,
        bench_remove_unordered,
        bench_resize_ports,
}
