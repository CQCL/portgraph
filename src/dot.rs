use std::fmt::Display;

use crate::PortIndex;

use super::graph::Graph;

pub trait DotEdge {
    fn style(&self) -> String {
        "None".to_string()
    }
}

pub fn dot_string<'a, N, P>(graph: &'a impl Graph<'a, N, P>) -> String
where
    N: 'a + Display + Clone,
    P: 'a + Display + Clone + DotEdge,
{
    let mut s = String::new();

    s.push_str("digraph {\n");

    for n in graph.nodes_iter() {
        let node = graph.node_weight(n).expect("missing node");
        s.push_str(&format!("{} [label=\"{:}\"]\n", n.index(), node)[..]);
        // TODO: Port weights
    }

    for from in graph.ports_iter() {
        let Some(to) = graph.port_link(from) else {continue};
        add_edge_str(graph, from, to, &mut s);
    }

    s.push_str("}\n");
    s
}

fn add_edge_str<'a, N, P>(
    graph: &'a impl Graph<'a, N, P>,
    from: PortIndex,
    to: PortIndex,
    dot_s: &mut String,
) where
    N: 'a + Display + Clone,
    P: 'a + Display + Clone + DotEdge,
{
    let from_node = graph.port_node(from).expect("missing node").index();
    let to_node = graph.port_node(to).expect("missing node").index();
    let from_offset = graph.port_offset(from).expect("missing offset");
    let to_offset = graph.port_offset(to).expect("missing offset");

    let style = graph.port_weight(from).unwrap().style();
    let edge_s = format!("{from_node} -> {to_node} [label=\"({from_offset}, {to_offset})\", style={style}]\n");
    dot_s.push_str(&edge_s[..])
}
