use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use portgraph::graph::{Graph, Direction};

fn make_line_graph(size: usize) -> Graph<usize, (usize, usize, usize)> {
    // TODO: preallocate capacity
    let mut graph = Graph::new();
    let mut prev_node = graph.add_node(0);

    for i in 1..size {
        let node = graph.add_node(i);
        let edge = graph.add_edge((i,i,i));
        let _ = graph.connect_last(prev_node, edge, Direction::Outgoing);
        let _ = graph.connect_last(node, edge, Direction::Incoming);
        prev_node = node;
    }

    graph
}

fn bench_make_portgraph(c: &mut Criterion) {
    let mut g = c.benchmark_group("graph creation");

    for size in [0, 10, 100, 1_000, 10_000, 100_000, 1_000_000] {
        g.bench_with_input(
            BenchmarkId::new("make_line_graph", size),
            &size,
            |b, size| b.iter(|| black_box(make_line_graph(*size))),
        );
    }
}

fn bench_clone_portgraph(c: &mut Criterion) {
    let mut g = c.benchmark_group("graph cloning");

    for size in [0, 10, 100, 1_000, 10_000, 100_000, 1_000_000] {
        g.bench_with_input(
            BenchmarkId::new("clone_line_graph", size),
            &size,
            |b, size| {
                let graph = make_line_graph(*size);
                b.iter(|| black_box(graph.clone()))
            },
        );
    }
}

criterion_group!(benches, bench_make_portgraph, bench_clone_portgraph);
criterion_main!(benches);
