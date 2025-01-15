#[allow(dead_code)]
mod benchmarks;

use criterion::criterion_main;

criterion_main! {
    // benchmarks::hierarchy::benches,
    // benchmarks::portgraph::benches,
    // benchmarks::render::benches,
    // benchmarks::toposort::benches,
    // benchmarks::convex::benches,
    benchmarks::hash::benches
}
