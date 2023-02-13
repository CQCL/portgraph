use std::fmt::Display;

use super::graph::{PortGraph, DIRECTIONS};

pub fn dot_string<N: Display, E: Display>(graph: &PortGraph<N, E>) -> String {
    let mut s = String::new();

    s.push_str("digraph {\n");

    for n in graph.nodes_iter() {
        let node = graph.node_weight(n).expect("missing node");
        s.push_str(&format!("{} [label=\"{:}\"]\n", n.index(), node)[..]);
    }

    let mut dangle_node_index = 0;
    for p in graph.ports_iter() {
        add_edge_str(graph, p, &mut s, &mut dangle_node_index);
    }

    s.push_str("}\n");
    s
}

fn add_edge_str<N: Display, E: Display>(
    graph: &PortGraph<N, E>,
    e: super::graph::EdgeIndex,
    dot_s: &mut String,
    node_count: &mut usize,
) {
    let [(b, bp), (a, ap)] = DIRECTIONS.map(|dir| {
        if let Some(n) = graph.edge_endpoint(e, dir) {
            (
                format!("{}", n.index()),
                format!(
                    "{}",
                    graph
                        .node_edges(n, dir)
                        .enumerate()
                        .find(|(_, oe)| *oe == e)
                        .expect("missing edge")
                        .0
                ),
            )
        } else {
            *node_count += 1;
            let node_id = format!("_{}", *node_count - 1);
            dot_s.push_str(&format!("{} [shape=point label=\"\"]\n", &node_id)[..]);

            (node_id, "".into())
        }
    });

    let edge = graph.edge_weight(e).expect("missing edge");
    let edge_s = format!("{a} -> {b} [label=\"({ap}, {bp}); {edge}\"]\n");
    dot_s.push_str(&edge_s[..])
}
