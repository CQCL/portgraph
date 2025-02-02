#[allow(dead_code)]
mod benchmarks;

use iai_callgrind::main;

use benchmarks::render::callgrind_group as render;
use benchmarks::toposort::callgrind_group as toposort;

main!(library_benchmark_groups = render, toposort);
