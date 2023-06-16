#![allow(clippy::unit_arg)] // Required for black_box uses

use criterion::{black_box, criterion_group, BatchSize, Criterion};
use portgraph::{
    substitute::{BoundedSubgraph, OpenGraph, Rewrite, WeightedRewrite},
    LinkView, NodeIndex, PortGraph, PortView,
};

use super::generators::*;

/// Creates a rewrite that replaces a single node with another node.
fn make_single_node_rewrite(graph: &PortGraph, node: NodeIndex) -> Rewrite {
    // Get the external boundary ports
    let incoming = graph.input_links(node).map(|(_, p)| p).collect::<Vec<_>>();
    let outgoing = graph.output_links(node).map(|(_, p)| p).collect::<Vec<_>>();

    // Create a replacement
    let mut g2 = PortGraph::with_capacity(1, incoming.len() + outgoing.len());
    let new_node = g2.add_node(incoming.len(), outgoing.len());
    let replacement_inputs = g2.inputs(new_node).collect();
    let replacement_outputs = g2.outputs(new_node).collect();

    Rewrite::new(
        BoundedSubgraph::new([node].into_iter().collect(), incoming, outgoing),
        OpenGraph::new(g2, replacement_inputs, replacement_outputs),
    )
}

/// Creates a weighted rewrite that replaces a single node with another node.
fn make_single_node_weighted_rewrite(
    graph: &PortGraph,
    node: NodeIndex,
) -> WeightedRewrite<usize, isize> {
    let rewrite = make_single_node_rewrite(graph, node);
    let replacement_weights = make_weights(&rewrite.replacement.graph);
    WeightedRewrite {
        rewrite,
        replacement_weights,
    }
}

fn bench_apply_rewrite(c: &mut Criterion) {
    let mut g = c.benchmark_group("rewrite a single node");

    let graph = make_line_graph(10);
    let weights = make_weights(&graph);
    let rewrite = make_single_node_rewrite(&graph, NodeIndex::new(3));
    let w_rewrite = make_single_node_weighted_rewrite(&graph, NodeIndex::new(3));

    g.bench_function("apply_rewrite", |b| {
        b.iter_batched(
            || (graph.clone(), rewrite.clone()),
            |(mut g, rewrite)| black_box(g.apply_rewrite(rewrite)),
            BatchSize::SmallInput,
        );
    });
    g.bench_function("apply_weighted_rewrite", |b| {
        b.iter_batched(
            || (graph.clone(), weights.clone(), w_rewrite.clone()),
            |(mut g, mut w, rewrite)| black_box(g.apply_weighted_rewrite(rewrite, &mut w)),
            BatchSize::SmallInput,
        );
    });
    g.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets =
        bench_apply_rewrite,
}
