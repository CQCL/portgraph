//! Wall-time benchmarks using criterion.

#[allow(dead_code)]
mod benchmarks;

use criterion::criterion_main;

criterion_main! {
    benchmarks::hierarchy::criterion_group,
    benchmarks::portgraph::criterion_group,
    benchmarks::render::criterion_group,
    benchmarks::toposort::criterion_group,
    benchmarks::convex::criterion_group,
}
