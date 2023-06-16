#![allow(clippy::unit_arg)] // Required for black_box uses

use criterion::{black_box, criterion_group, AxisScale, BenchmarkId, Criterion, PlotConfiguration};
use portgraph::NodeIndex;
use portgraph_hierarchy::Hierarchy;

use super::generators::*;

/// DFS traversal of all the nodes in a hierarchy tree starting from the root
fn traverse_hierarchy(hierarchy: &Hierarchy, root: NodeIndex) {
    let mut stack = vec![root];
    while let Some(node) = stack.pop() {
        black_box(node);
        for child in hierarchy.children(node) {
            stack.push(child);
        }
    }
}

fn bench_create_hierarchy(c: &mut Criterion) {
    let mut g = c.benchmark_group("initialize a tree hierarchy");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 10_000] {
        g.bench_with_input(
            BenchmarkId::new("initialize_tree_hierarchy", size),
            &size,
            |b, size| {
                let graph = make_two_track_dag(*size);
                b.iter(|| black_box(make_hierarchy(&graph)))
            },
        );
    }
    g.finish();
}

fn bench_traverse_hierarchy(c: &mut Criterion) {
    let mut g = c.benchmark_group("traverse a tree hierarchy");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 1_000, 100_000] {
        g.bench_with_input(
            BenchmarkId::new("traverse_tree_hierarchy", size),
            &size,
            |b, size| {
                let graph = make_two_track_dag(*size);
                let hierarchy = make_hierarchy(&graph);
                let root = NodeIndex::new(0);
                b.iter(|| black_box(traverse_hierarchy(&hierarchy, root)))
            },
        );
    }
    g.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets =
        bench_create_hierarchy,
        bench_traverse_hierarchy,
}
