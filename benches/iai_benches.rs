#[allow(dead_code)]
mod benchmarks;
mod helpers;

use iai_callgrind::main;

use benchmarks::convex::callgrind_group as convex;
use benchmarks::hierarchy::callgrind_group as hierarchy;
use benchmarks::portgraph::callgrind_group as portgraph;
use benchmarks::render::callgrind_group as render;
use benchmarks::toposort::callgrind_group as toposort;

main!(
    library_benchmark_groups = convex,
    hierarchy,
    portgraph,
    render,
    toposort
);
