#![allow(clippy::unit_arg)] // Required for black_box uses

use crate::helpers::*;

use criterion::{criterion_group, Criterion};
use portgraph::{PortGraph, PortMut, PortView};

// -----------------------------------------------------------------------------
// Benchmark functions
// -----------------------------------------------------------------------------

struct MakePortgraph {
    size: usize,
}
impl SizedBenchmark for MakePortgraph {
    fn name() -> &'static str {
        "make_line_graph"
    }

    fn setup(size: usize) -> Self {
        Self { size }
    }

    fn run(&self) -> impl Sized {
        make_line_graph(self.size)
    }

    fn sizes() -> &'static [usize] {
        &[100, 10_000, 1_000_000]
    }
}

struct ClonePortgraph {
    graph: PortGraph,
}
impl SizedBenchmark for ClonePortgraph {
    fn name() -> &'static str {
        "clone_line_graph"
    }

    fn setup(size: usize) -> Self {
        let graph = make_line_graph(size);
        Self { graph }
    }

    fn run(&self) -> impl Sized {
        self.graph.clone()
    }

    fn sizes() -> &'static [usize] {
        &[100, 10_000, 1_000_000]
    }
}

struct RemoveUnordered {
    graph: PortGraph,
}
impl SizedBenchmarkWithInput for RemoveUnordered {
    type State = PortGraph;

    fn name() -> &'static str {
        "remove_unordered"
    }

    fn setup(size: usize) -> Self {
        let graph = make_two_track_dag(size / 4);
        Self { graph }
    }

    fn prepare_run(&self) -> Self::State {
        self.graph.clone()
    }

    fn run(&self, mut graph: PortGraph) -> impl Sized {
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

        while graph.node_count() > 5 {
            remove_every_five(&mut graph);
        }
        // Remove all remaining nodes
        while graph.node_count() > 0 {
            let next = graph.nodes_iter().next().unwrap();
            graph.remove_node(next);
        }
        graph
    }
}

struct ResizePorts {
    graph: PortGraph,
    size: usize,
}
impl SizedBenchmarkWithInput for ResizePorts {
    type State = PortGraph;

    fn name() -> &'static str {
        "resize_ports"
    }

    fn setup(size: usize) -> Self {
        let graph = make_two_track_dag(size / 4);
        Self { graph, size }
    }

    fn prepare_run(&self) -> Self::State {
        self.graph.clone()
    }

    fn run(&self, mut graph: PortGraph) -> impl Sized {
        let amount = self.size;
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
}

// -----------------------------------------------------------------------------
// iai_callgrind definitions
// -----------------------------------------------------------------------------

sized_iai_benchmark!(callgrind_make_portgraph, MakePortgraph);
sized_iai_benchmark!(callgrind_clone_portgraph, ClonePortgraph);
sized_iai_benchmark_with_input!(callgrind_remove_unordered, RemoveUnordered);
sized_iai_benchmark_with_input!(callgrind_resize_ports, ResizePorts);

iai_callgrind::library_benchmark_group!(
    name = callgrind_group;
    benchmarks =
        callgrind_make_portgraph,
        callgrind_clone_portgraph,
        callgrind_remove_unordered,
        callgrind_resize_ports,
);

// -----------------------------------------------------------------------------
// Criterion definitions
// -----------------------------------------------------------------------------

criterion_group! {
    name = criterion_group;
    config = Criterion::default();
    targets =
        MakePortgraph::criterion,
        ClonePortgraph::criterion,
        RemoveUnordered::criterion,
        ResizePorts::criterion,
}
