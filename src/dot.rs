//! Functions to encode a `PortGraph` in dot format.

use std::fmt::Display;

use crate::{Direction, Hierarchy, LinkView, NodeIndex, PortIndex, Weights};

/// Style of an edge in a dot graph. Defaults to "None".
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NodeStyle {
    /// Ignore the node. No edges will be connected to it.
    Hidden,
    /// Draw a box with the label inside.
    Box(String),
}

impl NodeStyle {
    /// Show a node label with the default style.
    pub fn new(label: impl ToString) -> Self {
        Self::Box(label.to_string())
    }
}

impl Default for NodeStyle {
    fn default() -> Self {
        Self::Box(String::new())
    }
}

/// Style of an edge in a dot graph. Defaults to "None".
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PortStyle {
    /// Do not draw a label. Edges will be connected to the node.
    Hidden,
    /// Just the port label
    Text(String),
    /// Draw a box around the label
    Box(String),
}

impl PortStyle {
    /// Show a port label with the default style.
    pub fn new(label: impl ToString) -> Self {
        Self::Box(label.to_string())
    }
}

impl Default for PortStyle {
    fn default() -> Self {
        Self::Box(String::new())
    }
}

/// Style of an edge in a dot graph. Defaults to "None".
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum EdgeStyle {
    /// Normal line
    #[default]
    Solid,
    /// Dotted line
    Dotted,
    /// Dashed line
    Dashed,
    /// Custom style
    Custom(String),
}

impl EdgeStyle {
    /// Get the style as a graphviz style string
    pub fn as_str(&self) -> &str {
        match self {
            Self::Solid => "",
            Self::Dotted => "dotted",
            Self::Dashed => "dashed",
            Self::Custom(s) => s,
        }
    }
}

/// Encode portgraph and `Hierarchy` in dot format.
///
/// Calls the `nodes` and `ports` functions to get the labels for the nodes and ports.
/// The `ports` function also returns the style of the edge connected to a port.
///
/// Hierarchy relationships are shown as a separate tree of parent-child relationships
pub fn hier_graph_dot_string_with<G: LinkView>(
    graph: &G,
    forest: &Hierarchy,
    nodes: impl FnMut(NodeIndex) -> NodeStyle,
    ports: impl FnMut(PortIndex) -> PortStyle,
    edges: impl FnMut(G::LinkEndpoint, G::LinkEndpoint) -> EdgeStyle,
) -> String {
    let mut dot = String::new();

    dot.push_str("digraph {\n");

    node_and_edge_strings(graph, &mut dot, nodes, ports, edges);

    let hier_node_id = |n: NodeIndex| format!("hier{}", n.index());

    for n in graph.nodes_iter() {
        let node_str = format!(
            "{} [shape=plain label=\"{}\"]\n",
            hier_node_id(n),
            n.index()
        );
        dot.push_str(&node_str);

        // Connect the parent to any existing children
        forest.children(n).for_each(|child| {
            dot.push_str(&{
                let from_node = n;
                let to_node = child;
                format!(
                    "{} -> {}  [style = \"dashed\"] \n",
                    hier_node_id(from_node),
                    hier_node_id(to_node),
                )
            });
        });
    }

    dot.push_str("}\n");
    dot
}

/// Encode a portgraph and `Hierarchy` in dot format.
pub fn hier_graph_dot_string(graph: &impl LinkView, hierarchy: &Hierarchy) -> String {
    hier_graph_dot_string_with(
        graph,
        hierarchy,
        |n| NodeStyle::new(n.index()),
        |_| PortStyle::new(""),
        |_, _| EdgeStyle::Solid,
    )
}

/// Encode a portgraph in dot format.
pub fn dot_string(graph: &impl LinkView) -> String {
    dot_string_with(
        graph,
        |n| NodeStyle::new(n.index()),
        |_| PortStyle::new(""),
        |_, _| EdgeStyle::Solid,
    )
}

/// Encode a portgraph in dot format.
///
/// Uses the `weights` to label the nodes and ports.
pub fn dot_string_weighted<N, P>(graph: &impl LinkView, weights: &Weights<N, P>) -> String
where
    N: Display + Clone,
    P: Display + Clone,
{
    dot_string_with(
        graph,
        |n| NodeStyle::new(&weights.nodes[n]),
        |p| PortStyle::new(&weights.ports[p]),
        |_, _| EdgeStyle::Solid,
    )
}

/// Encode a portgraph in dot format.
///
/// Calls the `nodes` and `ports` functions to get the labels for the nodes and ports.
/// The `ports` function also returns the style of the edge connected to a port.
pub fn dot_string_with<G: LinkView>(
    graph: &G,
    nodes: impl FnMut(NodeIndex) -> NodeStyle,
    ports: impl FnMut(PortIndex) -> PortStyle,
    edges: impl FnMut(G::LinkEndpoint, G::LinkEndpoint) -> EdgeStyle,
) -> String {
    let mut dot = String::new();

    dot.push_str("digraph {\n");
    node_and_edge_strings(graph, &mut dot, nodes, ports, edges);
    dot.push_str("}\n");
    dot
}

/// Append the node and edge data in dot format to a string
fn node_and_edge_strings<G: LinkView>(
    graph: &G,
    dot_str: &mut String,
    mut nodes: impl FnMut(NodeIndex) -> NodeStyle,
    mut ports: impl FnMut(PortIndex) -> PortStyle,
    mut edges: impl FnMut(G::LinkEndpoint, G::LinkEndpoint) -> EdgeStyle,
) {
    for node in graph.nodes_iter() {
        // Format the node as a table
        let node_style = nodes(node);
        let NodeStyle::Box(node_label) = node_style else {
            // Ignore this node
            continue;
        };

        // Track the port counts for spacing
        let ins = graph.num_inputs(node).max(1);
        let outs = graph.num_outputs(node).max(1);
        let table_width = ins * outs;

        let inputs_row = get_ports_row_dot(graph, node, Direction::Incoming, outs, &mut ports);
        let outputs_row = get_ports_row_dot(graph, node, Direction::Outgoing, ins, &mut ports);

        let label_row = format!(
            "<tr><td align=\"text\" border=\"0\" colspan=\"{table_width}\">{node_label}</td></tr>"
        );

        let node_str = format!("{} [shape=plain label=<", node.index())
            + "<table border=\"1\">"
            + &inputs_row
            + &label_row
            + &outputs_row
            + "</table>"
            + ">]\n";
        dot_str.push_str(&node_str);

        // Connect the linked output ports
        graph
            .outputs(node)
            .flat_map(|port| graph.port_links(port))
            .map(|(from, to)| get_edge_dot(graph, node, from, to, &mut edges))
            .for_each(|edge| {
                dot_str.push_str(&edge);
            });
    }
}

/// Outputs an html table row with the ports of a node.
///
/// `num_others` is the number of ports in the other direction.
fn get_ports_row_dot<G: LinkView>(
    graph: &G,
    node: NodeIndex,
    direction: Direction,
    num_others: usize,
    mut ports: impl FnMut(PortIndex) -> PortStyle,
) -> String {
    if graph.num_ports(node, direction) == 0 {
        return String::new();
    }
    let dir = match direction {
        Direction::Incoming => "in",
        Direction::Outgoing => "out",
    };

    let separator = |label: &str| if label.is_empty() { "" } else { ": " };

    let mut ports_row = "<tr>".to_string();
    for (offset, port) in graph.ports(node, direction).enumerate() {
        let port_str = match ports(port) {
            PortStyle::Hidden =>
                format!("<td port=\"{dir}{offset}\" align=\"text\" colspan=\"0\"></td>"),
            PortStyle::Text(label) =>
                format!("<td port=\"{dir}{offset}\" align=\"text\" colspan=\"{num_others}\">{offset}{label}</td>"),
            PortStyle::Box(label) => format!(
                    "<td port=\"{dir}{offset}\" align=\"text\" colspan=\"{num_others}\" cellpadding=\"1\">{offset}{separator}{label}</td>",
                    separator = separator(&label),
                ),
        };
        ports_row.push_str(&port_str);
    }
    ports_row.push_str("</tr>");
    ports_row
}

/// If the port is linked, outputs the edge in dot format.
fn get_edge_dot<G: LinkView>(
    graph: &G,
    from_node: NodeIndex,
    from: G::LinkEndpoint,
    to: G::LinkEndpoint,
    mut edges: impl FnMut(G::LinkEndpoint, G::LinkEndpoint) -> EdgeStyle,
) -> String {
    let from_offset = graph.port_offset(from).expect("missing port").index();
    let to_node = graph.port_node(to).expect("missing node");
    let to_offset = graph.port_offset(to).expect("missing port").index();
    let edge_style = edges(from, to);
    let edge_label = edge_style.as_str();
    format!(
        "{}:out{} -> {}:in{} [style=\"{edge_label}\"]\n",
        from_node.index(),
        from_offset,
        to_node.index(),
        to_offset,
    )
}

#[cfg(test)]
mod tests {
    use crate::{PortGraph, PortView};

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
0:out0 -> 1:in0 [style=""]
0:out1 -> 2:in0 [style=""]
1 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="1" cellpadding="1">0</td></tr><tr><td align="text" border="0" colspan="1">1</td></tr></table>>]
2 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="1" cellpadding="1">0</td></tr><tr><td align="text" border="0" colspan="1">2</td></tr></table>>]
}
"#;
        assert_eq!(dot, expected);
    }

    #[test]
    fn test_hier_dot_string() {
        let mut graph = PortGraph::new();
        let n1 = graph.add_node(3, 2);
        let n2 = graph.add_node(1, 0);
        let n3 = graph.add_node(1, 0);
        graph.link_nodes(n1, 0, n2, 0).unwrap();
        graph.link_nodes(n1, 1, n3, 0).unwrap();

        let mut hier = Hierarchy::new();

        hier.push_child(n2, n1).unwrap();
        hier.push_child(n3, n1).unwrap();
        let dot = hier_graph_dot_string_with(
            &graph,
            &hier,
            |_| Default::default(),
            |_| Default::default(),
            |_, _| Default::default(),
        );
        let expected = r#"digraph {
0 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="2" cellpadding="1">0</td><td port="in1" align="text" colspan="2" cellpadding="1">1</td><td port="in2" align="text" colspan="2" cellpadding="1">2</td></tr><tr><td align="text" border="0" colspan="6"></td></tr><tr><td port="out0" align="text" colspan="3" cellpadding="1">0</td><td port="out1" align="text" colspan="3" cellpadding="1">1</td></tr></table>>]
0:out0 -> 1:in0 [style=""]
0:out1 -> 2:in0 [style=""]
1 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="1" cellpadding="1">0</td></tr><tr><td align="text" border="0" colspan="1"></td></tr></table>>]
2 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="1" cellpadding="1">0</td></tr><tr><td align="text" border="0" colspan="1"></td></tr></table>>]
hier0 [shape=plain label="0"]
hier0 -> hier1  [style = "dashed"] 
hier0 -> hier2  [style = "dashed"] 
hier1 [shape=plain label="1"]
hier2 [shape=plain label="2"]
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
0:out0 -> 1:in0 [style=""]
0:out1 -> 2:in0 [style=""]
1 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="1" cellpadding="1">0: in 0</td></tr><tr><td align="text" border="0" colspan="1">node2</td></tr></table>>]
2 [shape=plain label=<<table border="1"><tr><td port="in0" align="text" colspan="1" cellpadding="1">0: in 0</td></tr><tr><td align="text" border="0" colspan="1">node3</td></tr></table>>]
}
"#;
        assert_eq!(dot, expected);
    }
}
