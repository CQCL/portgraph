//! Functions to encode a `PortGraph` in dot format.

use std::fmt::Display;

use crate::{Direction, NodeIndex, PortGraph, PortIndex, Weights};

/// Style of an edge in a dot graph. Defaults to "None".
pub type DotEdgeStyle = Option<String>;

/// Encode a `PortGraph` in dot format.
pub fn dot_string(graph: &PortGraph) -> String {
    dot_string_with(graph, |n| n.index().to_string(), |_| ("".to_string(), None))
}

/// Encode a `PortGraph` in dot format.
///
/// Uses the `weights` to label the nodes and ports.
pub fn dot_string_weighted<N, P>(graph: &PortGraph, weights: &Weights<N, P>) -> String
where
    N: Display + Clone,
    P: Display + Clone,
{
    dot_string_with(
        graph,
        |n| weights.nodes[n].to_string(),
        |p| (weights.ports[p].to_string(), None),
    )
}

/// Encode a `PortGraph` in dot format.
///
/// Calls the `nodes` and `ports` functions to get the labels for the nodes and ports.
/// The `ports` function also returns the style of the edge connected to a port.
pub fn dot_string_with(
    graph: &PortGraph,
    mut nodes: impl FnMut(NodeIndex) -> String,
    mut ports: impl FnMut(PortIndex) -> (String, DotEdgeStyle),
) -> String {
    let mut dot_node = String::new();
    let mut dot_edge = String::new();

    dot_node.push_str("digraph {\n");

    for n in graph.nodes_iter() {
        // Format the node as a table

        // Track the port counts for spacing
        let ins = graph.num_inputs(n).max(1);
        let outs = graph.num_outputs(n).max(1);
        let table_width = ins*outs;

        let inputs_row = get_ports_row_dot(graph, n, Direction::Incoming, outs, &mut ports);
        let outputs_row = get_ports_row_dot(graph, n, Direction::Outgoing, ins, &mut ports);

        let node_label = nodes(n);
        let label_row = format!("<tr><td align=\"text\" border=\"0\" colspan=\"{table_width}\">{node_label}</td></tr>");

        let node_str = format!("{} [shape=plain label=<", n.index())
            + "<table border=\"1\">"
            + &inputs_row
            + &label_row
            + &outputs_row
            + "</table>"
            + ">]\n";
        dot_node.push_str(&node_str);

        // Connect the linked output ports
        graph
            .outputs(n)
            .enumerate()
            .flat_map(|(offset, port)| get_edge_dot(graph, n, port, offset, &mut ports))
            .for_each(|edge| {
                dot_edge.push_str(&edge);
            });
    }

    dot_node.push_str(&dot_edge);
    dot_node.push_str("}\n");
    dot_node
}

/// Outputs an html table row with the ports of a node.
/// 
/// `num_others` is the number of ports in the other direction.
fn get_ports_row_dot(
    graph: &PortGraph,
    node: NodeIndex,
    direction: Direction,
    num_others: usize,
    mut ports: impl FnMut(PortIndex) -> (String, DotEdgeStyle),
) -> String {
    if graph.num_ports(node, direction) == 0 {
        return String::new();
    }
    let dir = match direction {
        Direction::Incoming => "in",
        Direction::Outgoing => "out",
    };

    let mut ports_row = "<tr>".to_string();
    for (offset, port) in graph.ports(node, direction).enumerate() {
        let (port_label, _) = ports(port);
        ports_row.push_str(&format!(
            "<td port=\"{dir}{offset}\" align=\"text\" colspan=\"{num_others}\" cellpadding=\"1\">{offset}{separator}{port_label}</td>",
            separator = if port_label.is_empty() { "" } else { ": " },
        ));
    }
    ports_row.push_str("</tr>");
    ports_row
}

/// If the port is linked, outputs the edge in dot format.
fn get_edge_dot(
    graph: &PortGraph,
    from_node: NodeIndex,
    from_port: PortIndex,
    from_offset: usize,
    mut ports: impl FnMut(PortIndex) -> (String, DotEdgeStyle),
) -> Option<String> {
    let to_port = graph.port_link(from_port)?;
    let to_node = graph.port_node(to_port).expect("missing node");
    let to_offset = graph.port_offset(to_port).expect("missing port");
    let edge_style = ports(from_port).1.unwrap_or("None".to_string());
    Some(format!(
        "{}:out{} -> {}:in{} [style={edge_style}]\n",
        from_node.index(),
        from_offset,
        to_node.index(),
        to_offset,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dot_string() {
        let mut graph = PortGraph::new();
        let n1 = graph.add_node(3, 2);
        let n2 = graph.add_node(1, 0);
        let n3 = graph.add_node(1, 0);
        graph.link_nodes(n1, 0, n2, 0).unwrap();
        graph.link_nodes(n1, 1, n3, 0).unwrap();

        let dot = dot_string(&graph);
        let expected = r#"digraph {
0 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="2" cellpadding="1">0</td><td port="in1" align="text" colspan="2" cellpadding="1">1</td><td port="in2" align="text" colspan="2" cellpadding="1">2</td></tr><tr><td align="text" border="0" colspan="6">0</td></tr><tr><td port="out0" align="text" colspan="3" cellpadding="1">0</td><td port="out1" align="text" colspan="3" cellpadding="1">1</td></tr></table>>]
1 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="1" cellpadding="1">0</td></tr><tr><td align="text" border="0" colspan="1">1</td></tr></table>>]
2 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="1" cellpadding="1">0</td></tr><tr><td align="text" border="0" colspan="1">2</td></tr></table>>]
0:out0 -> 1:in0 [style=None]
0:out1 -> 2:in0 [style=None]
}
"#;
        assert_eq!(dot, expected);
    }

    #[test]
    fn test_dot_string_weighted() {
        let mut graph = PortGraph::new();
        let n1 = graph.add_node(0, 2);
        let n2 = graph.add_node(1, 0);
        let n3 = graph.add_node(1, 0);
        let p10 = graph.output(n1, 0).unwrap();
        let p11 = graph.output(n1, 1).unwrap();
        let p20 = graph.input(n2, 0).unwrap();
        let p30 = graph.input(n3, 0).unwrap();

        graph.link_ports(p10, p20).unwrap();
        graph.link_ports(p11, p30).unwrap();

        let mut weights = Weights::new();
        weights[n1] = "node1".to_string();
        weights[n2] = "node2".to_string();
        weights[n3] = "node3".to_string();
        weights[p10] = "out 0".to_string();
        weights[p11] = "out 1".to_string();
        weights[p20] = "in 0".to_string();
        weights[p30] = "in 0".to_string();

        let dot = dot_string_weighted(&graph, &weights);
        println!("\n{}\n", dot);
        let expected = r#"digraph {
0 [shape=plain label=<<table border="1"><tr><td align="text" border="0" colspan="2">node1</td></tr><tr><td port="out0" align="text" colspan="1" cellpadding="1">0: out 0</td><td port="out1" align="text" colspan="1" cellpadding="1">1: out 1</td></tr></table>>]
1 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="1" cellpadding="1">0: in 0</td></tr><tr><td align="text" border="0" colspan="1">node2</td></tr></table>>]
2 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="1" cellpadding="1">0: in 0</td></tr><tr><td align="text" border="0" colspan="1">node3</td></tr></table>>]
0:out0 -> 1:in0 [style=None]
0:out1 -> 2:in0 [style=None]
}
"#;
        assert_eq!(dot, expected);
    }
}
