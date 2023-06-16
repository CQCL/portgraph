#[allow(dead_code)]
mod benchmarks;

use criterion::criterion_main;

criterion_main! {
    benchmarks::portgraph::benches,
    benchmarks::substitute::benches,
}
