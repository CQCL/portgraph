//! Functions to encode a `PortGraph` in dot format.

use std::fmt::Display;

use itertools::Itertools;

use crate::{Direction, Hierarchy, LinkView, NodeIndex, PortIndex, Weights};

use super::{EdgeStyle, NodeStyle, PortStyle, PresentationStyle};

/// Configurable mermaid formatter for a `PortGraph`.
pub struct DotFormatter<'g, G: LinkView> {
    graph: &'g G,
    forest: Option<&'g Hierarchy>,
    node_style: Option<Box<dyn FnMut(NodeIndex) -> NodeStyle + 'g>>,
    port_style: Option<Box<dyn FnMut(PortIndex) -> PortStyle + 'g>>,
    #[allow(clippy::type_complexity)]
    edge_style: Option<Box<dyn FnMut(G::LinkEndpoint, G::LinkEndpoint) -> EdgeStyle + 'g>>,
}

impl<'g, G> DotFormatter<'g, G>
where
    G: LinkView,
{
    /// Initialize a new `DotFormatter` for `graph`.
    pub fn new(graph: &'g G) -> Self {
        Self {
            graph,
            forest: None,
            node_style: None,
            port_style: None,
            edge_style: None,
        }
    }

    /// Set the `Hierarchy` to use for the graph.
    pub fn with_hierarchy(mut self, forest: &'g Hierarchy) -> Self {
        self.forest = Some(forest);
        self
    }

    /// Set the function to use to get the style of a node.
    pub fn with_node_style(mut self, node_style: impl FnMut(NodeIndex) -> NodeStyle + 'g) -> Self {
        self.node_style = Some(Box::new(node_style));
        self
    }

    /// Set the function to use to get the style of a port.
    pub fn with_port_style(mut self, port_style: impl FnMut(PortIndex) -> PortStyle + 'g) -> Self {
        self.port_style = Some(Box::new(port_style));
        self
    }

    /// Set the function to use to get the style of an edge.
    pub fn with_edge_style(
        mut self,
        edge_style: impl FnMut(G::LinkEndpoint, G::LinkEndpoint) -> EdgeStyle + 'g,
    ) -> Self {
        self.edge_style = Some(Box::new(edge_style));
        self
    }

    /// Encode some `Weights` in the dot format.
    ///
    /// This is a convenience method to set the node and port styles based on the weight values.
    /// It overrides any previous node or port style set.
    pub fn with_weights<'w, N, P>(self, weights: &'w Weights<N, P>) -> Self
    where
        'w: 'g,
        N: Display + Clone,
        P: Display + Clone,
    {
        self.with_node_style(|n| NodeStyle::boxed(&weights.nodes[n]))
            .with_port_style(|p| PortStyle::new(&weights.ports[p]))
    }

    /// Encode the graph in dot format.
    pub fn finish(mut self) -> String {
        let mut dot = String::new();

        dot.push_str("digraph {\n");
        self.node_and_edge_strings(&mut dot);
        self.hierarchy_strings(&mut dot);
        dot.push_str("}\n");

        dot
    }

    /// Get the style of a node, using a default if none is set.
    fn node_style(&mut self, node: NodeIndex) -> NodeStyle {
        self.node_style
            .as_mut()
            .map(|f| f(node))
            .unwrap_or_else(|| NodeStyle::boxed(node.index().to_string()))
    }

    /// Get the style of a port, using a default if none is set.
    fn port_style(&mut self, port: PortIndex) -> PortStyle {
        self.port_style
            .as_mut()
            .map(|f| f(port))
            .unwrap_or_default()
    }

    /// Get the style of an edge, using a default if none is set.
    fn edge_style(&mut self, src: G::LinkEndpoint, dst: G::LinkEndpoint) -> EdgeStyle {
        self.edge_style
            .as_mut()
            .map(|f| f(src, dst))
            .unwrap_or_default()
    }

    /// Append the node and edge data in dot format to a string
    fn node_and_edge_strings(&mut self, dot: &mut String) {
        for node in self.graph.nodes_iter() {
            // Format the node as a table
            let node_style = self.node_style(node);
            let (node_label, attrs) = match node_style {
                NodeStyle::Boxed { label, attrs } => (label, attrs),
                #[allow(deprecated)]
                NodeStyle::Box(label) => (label, PresentationStyle::new()),
                NodeStyle::Hidden => {
                    // Ignore this node
                    continue;
                }
            };

            // Get the ports to render, ignoring Hidden ones.
            let ins = self.get_port_strings(node, Direction::Incoming);
            let outs = self.get_port_strings(node, Direction::Outgoing);
            let ins_len = ins.len().max(1);
            let outs_len = outs.len().max(1);
            let table_width = ins_len * outs_len;

            let inputs_row = self.get_ports_row_dot(&ins, outs_len);
            let outputs_row = self.get_ports_row_dot(&outs, ins_len);

            let label_row = format!(
                "<tr><td align=\"text\" border=\"0\" colspan=\"{table_width}\">{node_label}</td></tr>"
            );

            let node_str = String::new()
                + &node.index().to_string()
                + " [shape=plain "
                + &encode_presentation_attrs(&attrs)
                + "label=<"
                + "<table border=\"1\">"
                + &inputs_row
                + &label_row
                + &outputs_row
                + "</table>"
                + ">]\n";
            dot.push_str(&node_str);

            // Connect the linked output ports
            self.graph
                .outputs(node)
                .flat_map(|port| self.graph.port_links(port))
                .map(|(from, to)| self.get_edge_dot(node, from, to))
                .for_each(|edge| {
                    dot.push_str(&edge);
                });
        }
    }

    /// Compute the rendered port styles for a node. Returns a vector with a
    /// port id, a cell style string, and a label for ports to be shown.
    fn get_port_strings(&mut self, node: NodeIndex, direction: Direction) -> Vec<PortCellStrings> {
        let dir = match direction {
            Direction::Incoming => "in",
            Direction::Outgoing => "out",
        };
        let make_label = |offset: usize, show_offset: bool, label: &str| match (show_offset, label)
        {
            (false, label) => label.to_string(),
            (true, "") => format!("{offset}"),
            (true, label) => format!("{offset}: {label}"),
        };
        self.graph
            .ports(node, direction)
            .enumerate()
            .filter_map(|(offset, port)| match self.port_style(port) {
                PortStyle::Hidden => None,
                PortStyle::Plain(label, show_offset) => Some(PortCellStrings {
                    id: format!("{dir}{offset}"),
                    style: "border=\"0\"".to_string(),
                    label: make_label(offset, show_offset, &label),
                }),
                PortStyle::Boxed(label, show_offset) => Some(PortCellStrings {
                    id: format!("{dir}{offset}"),
                    style: String::new(),
                    label: make_label(offset, show_offset, &label),
                }),
            })
            .collect()
    }

    /// Outputs an html table row with the ports of a node.
    ///
    /// `num_others` is the number of ports in the other direction.
    ///
    /// The node table is a grid with `#inputs * #outputs` columns, so each port
    /// label should be `num_others` columns wide.
    fn get_ports_row_dot(&mut self, ports: &Vec<PortCellStrings>, num_others: usize) -> String {
        if ports.is_empty() {
            return String::new();
        }
        let mut ports_row = "<tr>".to_string();
        for PortCellStrings { id, style, label } in ports {
            ports_row.push_str(&format!(
                "<td port=\"{id}\" align=\"text\" colspan=\"{num_others}\" cellpadding=\"1\" {style}>{label}</td>"
            ));
        }
        ports_row.push_str("</tr>");
        ports_row
    }

    /// If the port is linked, outputs the edge in dot format.
    fn get_edge_dot(
        &mut self,
        from_node: NodeIndex,
        from: G::LinkEndpoint,
        to: G::LinkEndpoint,
    ) -> String {
        let from_offset = self.graph.port_offset(from).expect("missing port").index();
        let to_node = self.graph.port_node(to).expect("missing node");
        let to_offset = self.graph.port_offset(to).expect("missing port").index();
        let edge_style = self.edge_style(from, to);
        let edge_label = edge_style.as_dot_str();
        format!(
            "{}:out{} -> {}:in{} [style=\"{edge_label}\"]\n",
            from_node.index(),
            from_offset,
            to_node.index(),
            to_offset,
        )
    }

    fn hierarchy_strings(&mut self, dot: &mut String) {
        if let Some(forest) = self.forest {
            let hier_node_id = |n: NodeIndex| format!("hier{}", n.index());

            for n in self.graph.nodes_iter() {
                let node_str = format!(
                    "{} [shape=plain label=\"{}\"]\n",
                    hier_node_id(n),
                    n.index()
                );
                dot.push_str(&node_str);

                // Connect the parent to any existing children
                forest
                    .children(n)
                    .filter(|&c| self.graph.contains_node(c))
                    .for_each(|child| {
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
        }
    }
}

/// A trait for encoding a graph in dot format.
pub trait DotFormat: LinkView + Sized {
    /// Initialize a `DotFormatter` for the graph.
    fn dot_format(&self) -> DotFormatter<'_, Self>;

    /// Encode the graph in dot format.
    fn dot_string(&self) -> String {
        self.dot_format().finish()
    }
}

impl<G> DotFormat for G
where
    G: LinkView,
{
    fn dot_format(&self) -> DotFormatter<'_, Self> {
        DotFormatter::new(self)
    }
}

/// Struct used internally while formatting a port in a node.
struct PortCellStrings {
    /// The id for the cell containing the port.
    pub id: String,
    /// Extra style options to use in the port's table cell.
    pub style: String,
    /// The label to show for the port.
    pub label: String,
}

/// Encode a [`PresentationStyle`] into dot attributes.
pub fn encode_presentation_attrs(attrs: &PresentationStyle) -> String {
    let mut result = Vec::new();
    if let Some(color) = &attrs.color {
        result.push(format!("fontcolor=\"{color}\" "));
    }
    if let Some(fill) = &attrs.fill {
        result.push(format!("fillcolor=\"{fill}\" "));
    }
    if let Some(stroke) = &attrs.stroke {
        result.push(format!("color=\"{stroke}\" "));
    }
    if let Some(stroke_width) = &attrs.stroke_width {
        result.push(format!("penwidth=\"{stroke_width}\" "));
    }
    result.into_iter().join("")
}
