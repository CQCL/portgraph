#[allow(dead_code)]
mod benchmarks;

use criterion::criterion_main;

criterion_main! {
    benchmarks::portgraph::portgraph_benches,
    benchmarks::substitute::substitute_benches,
}
