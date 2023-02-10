use criterion::{
    black_box, criterion_group, criterion_main, AxisScale, BenchmarkId, Criterion,
    PlotConfiguration,
};
use portgraph::{graph::Graph, portgraph::PortGraph, Direction};

fn make_line_graph(size: usize) -> PortGraph {
    let mut graph = PortGraph::with_capacity(size, size * 2);
    let mut prev_node = graph.add_node(2, 2);

    for _ in 1..size {
        let node = graph.add_node(2, 2);

        for i in 0..1 {
            let port_from = graph.outputs(prev_node).nth(i).unwrap();
            let port_to = graph.inputs(node).nth(i).unwrap();
            graph.link_ports(port_from, port_to).unwrap();
        }

        prev_node = node;
    }

    graph
}

fn make_line_graph_old(size: usize) -> Graph<(), ()> {
    let mut graph = Graph::with_capacity(size, size * 2);
    let edge0 = graph.add_edge(());
    let edge1 = graph.add_edge(());
    let mut prev_node = graph.add_node_with_edges((), [], [edge0, edge1]).unwrap();

    for _ in 1..size {
        let mut node_edges = graph.node_edges(prev_node, Direction::Outgoing);
        let edge_in0 = node_edges.next().unwrap();
        let edge_in1 = node_edges.next().unwrap();
        drop(node_edges);
        let edge_out0 = graph.add_edge(());
        let edge_out1 = graph.add_edge(());
        let node = graph
            .add_node_with_edges((), [edge_in0, edge_in1], [edge_out0, edge_out1])
            .unwrap();
        prev_node = node;
    }

    graph
}

/// Create an acyclic graph with `layer` layers and 2 nodes per layer, connected sequentially as follows.
///
/// o ---> o ---> o ---> o ---> o   ...
/// |                    |
/// v                    v
/// o ---> o ---> o ---> o ---> o   ...
///
fn make_two_track_dag(layers: usize) -> Graph<usize, (usize, usize, usize)> {
    let mut graph = Graph::with_capacity(layers, layers + layers / 3);
    if layers == 0 {
        return graph;
    } else if layers == 1 {
        graph.add_node(0);
        graph.add_node(1);
        return graph;
    }

    let mut prev_edges = [graph.add_edge((42, 0, 24)), graph.add_edge((42, 0, 24))];
    graph.add_node_with_edges(0, [], [prev_edges[0]]).unwrap();
    graph.add_node_with_edges(1, [], [prev_edges[1]]).unwrap();

    for layer in 1..(layers - 1) {
        let i = layer * 2;
        let new_edges = [graph.add_edge((42, i, 24)), graph.add_edge((42, i + 1, 24))];
        let node0 = graph
            .add_node_with_edges(i, [prev_edges[0]], [new_edges[0]])
            .unwrap();
        let node1 = graph
            .add_node_with_edges(i + 1, [prev_edges[1]], [new_edges[1]])
            .unwrap();
        // Add an edge connecting both nodes every third layer
        if layer % 3 == 0 {
            let edge = graph.add_edge((42, 0, 24));
            graph
                .connect_last(node0, edge, Direction::Outgoing)
                .unwrap();
            graph
                .connect_last(node1, edge, Direction::Incoming)
                .unwrap();
        }
        prev_edges = new_edges;
    }
    graph
        .add_node_with_edges(layers * 2 - 2, [prev_edges[0]], [])
        .unwrap();
    graph
        .add_node_with_edges(layers * 2 - 1, [prev_edges[1]], [])
        .unwrap();

    graph
}

/// Remove one every five nodes from the graph.
fn remove_every_five(graph: &mut Graph<usize, (usize, usize, usize)>) {
    let mut to_remove = Vec::with_capacity(graph.node_count());
    for (i, v) in graph.node_indices().enumerate() {
        if i % 5 == 0 {
            to_remove.push(v);
        }
    }
    for node in to_remove {
        graph.remove_node(node);
    }
}

/// Remove nodes from the graph in an unordered way until it is empty.
fn remove_all_unordered(graph: &mut Graph<usize, (usize, usize, usize)>) {
    while graph.node_count() > 5 {
        remove_every_five(graph);
    }
    // Remove all remaining nodes
    while graph.node_count() > 0 {
        graph.remove_node(graph.node_indices().next().unwrap());
    }
}

fn bench_make_portgraph(c: &mut Criterion) {
    let mut g = c.benchmark_group("graph creation");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [100, 10_000, 1_000_000] {
        g.bench_with_input(
            BenchmarkId::new("make_line_graph_old", size),
            &size,
            |b, size| b.iter(|| black_box(make_line_graph_old(*size))),
        );
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

criterion_group!(
    benches,
    bench_make_portgraph,
    // bench_clone_portgraph,
    // bench_remove_unordered
);
criterion_main!(benches);
