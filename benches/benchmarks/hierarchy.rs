#![allow(clippy::unit_arg)] // Required for black_box uses

use criterion::{black_box, criterion_group, Criterion};
use portgraph::{Hierarchy, NodeIndex, PortGraph};

use crate::helpers::*;

// -----------------------------------------------------------------------------
// Benchmark functions
// -----------------------------------------------------------------------------

struct CreateHierarchy {
    graph: PortGraph,
}
impl SizedBenchmark for CreateHierarchy {
    fn name() -> &'static str {
        "initialize_tree_hierarchy"
    }

    fn setup(size: usize) -> Self {
        let graph = make_two_track_dag(size);
        Self { graph }
    }

    fn run(&self) -> impl Sized {
        make_hierarchy(&self.graph)
    }
}

struct TraverseHierarchy {
    hierarchy: Hierarchy,
    root: NodeIndex,
}
impl SizedBenchmark for TraverseHierarchy {
    fn name() -> &'static str {
        "traverse_tree_hierarchy"
    }

    fn setup(size: usize) -> Self {
        let graph = make_two_track_dag(size);
        let hierarchy = make_hierarchy(&graph);
        let root = NodeIndex::new(0);
        Self { hierarchy, root }
    }

    fn run(&self) -> impl Sized {
        let mut stack = vec![self.root];
        while let Some(node) = stack.pop() {
            black_box(node);
            for child in self.hierarchy.children(node) {
                stack.push(child);
            }
        }
    }
}

// -----------------------------------------------------------------------------
// iai_callgrind definitions
// -----------------------------------------------------------------------------

sized_iai_benchmark!(callgrind_create_hierarchy, CreateHierarchy);
sized_iai_benchmark!(callgrind_traverse_hierarchy, TraverseHierarchy);

iai_callgrind::library_benchmark_group!(
    name = callgrind_group;
    benchmarks =
        callgrind_create_hierarchy,
        callgrind_traverse_hierarchy,
);

// -----------------------------------------------------------------------------
// Criterion definitions
// -----------------------------------------------------------------------------

criterion_group! {
    name = criterion_group;
    config = Criterion::default();
    targets =
        CreateHierarchy::criterion,
        TraverseHierarchy::criterion,
}
