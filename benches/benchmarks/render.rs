//! Benchmarks for the graph renderers.

use criterion::{criterion_group, Criterion};
use portgraph::render::{DotFormat, MermaidFormat};
use portgraph::{Hierarchy, PortGraph, Weights};

use crate::helpers::*;

// -----------------------------------------------------------------------------
// Benchmark functions
// -----------------------------------------------------------------------------

struct RenderMermaid {
    graph: PortGraph,
    hierarchy: Hierarchy,
    weights: Weights<usize, isize>,
}
impl SizedBenchmark for RenderMermaid {
    fn name() -> &'static str {
        "render_mermaid"
    }

    fn setup(size: usize) -> Self {
        let graph = make_two_track_dag(size);
        let hierarchy = make_hierarchy(&graph);
        let weights = make_weights(&graph);
        Self {
            graph,
            hierarchy,
            weights,
        }
    }

    fn run(&self) -> impl Sized {
        self.graph
            .mermaid_format()
            .with_hierarchy(&self.hierarchy)
            .with_weights(&self.weights)
            .finish()
    }
}

struct RenderDot {
    graph: PortGraph,
    hierarchy: Hierarchy,
    weights: Weights<usize, isize>,
}
impl SizedBenchmark for RenderDot {
    fn name() -> &'static str {
        "render_dot"
    }

    fn setup(size: usize) -> Self {
        let graph = make_two_track_dag(size);
        let hierarchy = make_hierarchy(&graph);
        let weights = make_weights(&graph);
        Self {
            graph,
            hierarchy,
            weights,
        }
    }

    fn run(&self) -> impl Sized {
        self.graph
            .dot_format()
            .with_hierarchy(&self.hierarchy)
            .with_weights(&self.weights)
            .finish()
    }
}

// -----------------------------------------------------------------------------
// iai_callgrind definitions
// -----------------------------------------------------------------------------

sized_iai_benchmark!(callgrind_render_mermaid, RenderMermaid);
sized_iai_benchmark!(callgrind_render_dot, RenderDot);

iai_callgrind::library_benchmark_group!(
    name = callgrind_group;
    benchmarks = callgrind_render_dot, callgrind_render_mermaid
);

// -----------------------------------------------------------------------------
// Criterion definitions
// -----------------------------------------------------------------------------

criterion_group! {
    name = criterion_group;
    config = Criterion::default();
    targets =
        RenderMermaid::criterion,
        RenderDot::criterion,
}
