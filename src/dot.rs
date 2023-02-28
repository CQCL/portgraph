use std::fmt::Display;

use crate::{PortGraph, PortIndex, Weights};

pub trait DotEdge {
    fn style(&self) -> String {
        "None".to_string()
    }
}

pub fn dot_string(graph: &PortGraph) -> String {
    make_dot_string::<EmptyWeights, EmptyWeights>(graph, None)
}

pub fn dot_string_weighted<N, P>(graph: &PortGraph, weights: &Weights<N, P>) -> String
where
    N: Display + Clone,
    P: Display + Clone + DotEdge,
{
    make_dot_string(graph, Some(weights))
}

fn make_dot_string<N, P>(graph: &PortGraph, weights: Option<&Weights<N, P>>) -> String
where
    N: Display + Clone,
    P: Display + Clone + DotEdge,
{
    let mut s = String::new();

    s.push_str("digraph {\n");

    for n in graph.nodes_iter() {
        if let Some(w) = weights {
            let node_weight = &w.nodes[n];
            s.push_str(&format!("{} [label=\"({:})\"]\n", n.index(), node_weight)[..]);
            // TODO: Port weights are not displayed. Define how to encode them
            // in the dot file.
        } else {
            s.push_str(&format!("{} \n", n.index())[..]);
        }
    }

    for from in graph.ports_iter() {
        let Some(to) = graph.port_link(from) else {continue};
        add_edge_str(graph, weights, from, to, &mut s);
    }

    s.push_str("}\n");
    s
}

fn add_edge_str<N, P>(
    graph: &PortGraph,
    weights: Option<&Weights<N, P>>,
    from: PortIndex,
    to: PortIndex,
    dot_s: &mut String,
) where
    N: Display + Clone,
    P: Display + Clone + DotEdge,
{
    let from_node = graph.port_node(from).expect("missing node").index();
    let to_node = graph.port_node(to).expect("missing node").index();
    let from_offset = graph.port_offset(from).expect("missing offset");
    let to_offset = graph.port_offset(to).expect("missing offset");

    let style = if let Some(w) = weights {
        w.ports[from].style()
    } else {
        "None".to_string()
    };

    let edge_s = format!(
        "{from_node} -> {to_node} [label=\"({from_offset}, {to_offset})\", style={style}]\n"
    );
    dot_s.push_str(&edge_s[..])
}

#[derive(Debug, Clone, Copy)]
struct EmptyWeights;

impl DotEdge for EmptyWeights {}

impl Display for EmptyWeights {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "")
    }
}
