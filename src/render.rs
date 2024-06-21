//! This module contains rendering logic from portgraphs into graphviz and
//! mermaid diagrams.

mod dot;
mod mermaid;

use std::borrow::Cow;

pub use dot::{DotFormat, DotFormatter};
pub use mermaid::{MermaidFormat, MermaidFormatter};

use self::mermaid::encode_label;

/// Style of a rendered edge.
///
/// Defaults to a box with no label.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
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

/// Style of an edge in a rendered graph. Defaults to a box with no label.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum PortStyle {
    /// Do not draw a label. Edges will be connected to the node.
    Hidden,
    /// Just the port label. Optionally prepend the port index.
    Plain(String, bool),
    /// Draw a box around the label. Optionally prepend the port index.
    Boxed(String, bool),
}

impl PortStyle {
    /// Show a port label with the default style.
    pub fn new(label: impl ToString) -> Self {
        Self::Boxed(label.to_string(), true)
    }

    /// Just the port label. Optionally prepend the port index.
    pub fn text(label: impl ToString, show_offset: bool) -> Self {
        Self::Plain(label.to_string(), show_offset)
    }

    /// Draw a box around the label. Optionally prepend the port index.
    pub fn boxed(label: impl ToString, show_offset: bool) -> Self {
        Self::Boxed(label.to_string(), show_offset)
    }
}

impl Default for PortStyle {
    fn default() -> Self {
        Self::Boxed(String::new(), true)
    }
}

/// Style of an edge in a rendered graph. Defaults to [`EdgeStyle::Solid`].
#[derive(Clone, Debug, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum EdgeStyle {
    /// Normal line
    #[default]
    Solid,
    /// Dotted line
    Dotted,
    /// Dashed line
    Dashed,
    /// Edge style with a label
    Labelled(String, Box<EdgeStyle>),
    /// Custom style
    Custom(String),
}

impl EdgeStyle {
    /// Adds a label to the edge style.
    ///
    /// If the edge style already has a label, it will be replaced.
    pub fn with_label(self, label: impl ToString) -> Self {
        match self {
            Self::Labelled(_, e) => Self::Labelled(label.to_string(), e),
            _ => Self::Labelled(label.to_string(), Box::new(self)),
        }
    }

    /// Returns the base style of the edge, without labels.
    pub fn strip_label(&self) -> &Self {
        match self {
            Self::Labelled(_, e) => e.strip_label(),
            e => e,
        }
    }

    /// Get the style as a graphviz style string
    pub(super) fn as_dot_str(&self) -> &str {
        match self {
            Self::Solid => "",
            Self::Dotted => "dotted",
            Self::Dashed => "dashed",
            Self::Custom(s) => s,
            // Ignore edge labels.
            Self::Labelled(_lbl, e) => e.as_dot_str(),
        }
    }

    /// Get the style as a graphviz style string
    pub(super) fn as_mermaid_str(&self) -> Cow<'_, str> {
        match self {
            Self::Solid => "-->".into(),
            Self::Dotted => "-.->".into(),
            // Dashed links are not supported in mermaid, we use dots instead.
            Self::Dashed => "-.->".into(),
            Self::Custom(s) => s.into(),
            Self::Labelled(lbl, e) => {
                let lbl = encode_label("", lbl);
                match e.strip_label() {
                    Self::Solid => format!("--{}-->", lbl).into(),
                    Self::Dotted => format!("-.{}.->", lbl).into(),
                    Self::Dashed => format!("-.{}.->", lbl).into(),
                    Self::Custom(s) => s.into(),
                    Self::Labelled(_, _) => {
                        unreachable!("`strip_label` cannot return a `Labelled`")
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use std::fmt::Display;

    use rstest::{fixture, rstest};

    use crate::{Hierarchy, LinkMut, PortGraph, PortMut, PortView, Weights};

    use super::{DotFormat, MermaidFormat};

    /// A simple flat graph with some nodes and edges.
    #[fixture]
    fn flat_graph() -> (
        &'static str,
        PortGraph,
        Option<Hierarchy>,
        Option<Weights<String, String>>,
    ) {
        let mut graph = PortGraph::new();
        let n1 = graph.add_node(3, 2);
        let n2 = graph.add_node(1, 0);
        let n3 = graph.add_node(1, 0);
        graph.link_nodes(n1, 0, n2, 0).unwrap();
        graph.link_nodes(n1, 1, n3, 0).unwrap();
        ("flat", graph, None, None)
    }

    #[fixture]
    fn hierarchy_graph() -> (
        &'static str,
        PortGraph,
        Option<Hierarchy>,
        Option<Weights<String, String>>,
    ) {
        let mut graph = PortGraph::new();
        let n1 = graph.add_node(3, 2);
        let n2 = graph.add_node(0, 1);
        let n3 = graph.add_node(1, 0);
        graph.link_nodes(n2, 0, n3, 0).unwrap();

        let mut hier = Hierarchy::new();
        hier.push_child(n2, n1).unwrap();
        hier.push_child(n3, n1).unwrap();

        ("hierarchy", graph, Some(hier), None)
    }

    /// A hierarchical graph with edges between different regions.
    #[fixture]
    fn hierarchy_interregional_graph() -> (
        &'static str,
        PortGraph,
        Option<Hierarchy>,
        Option<Weights<String, String>>,
    ) {
        let mut graph = PortGraph::new();
        let n1 = graph.add_node(3, 2);
        let n2 = graph.add_node(0, 1);
        let n3 = graph.add_node(1, 0);
        let n4 = graph.add_node(1, 1);
        let n5 = graph.add_node(1, 1);
        graph.link_nodes(n2, 0, n3, 0).unwrap();
        graph.link_nodes(n4, 0, n5, 0).unwrap();

        let mut hier = Hierarchy::new();
        hier.push_child(n2, n1).unwrap();
        hier.push_child(n3, n1).unwrap();
        hier.push_child(n4, n2).unwrap();
        hier.push_child(n5, n3).unwrap();

        ("hierarchy_interregional", graph, Some(hier), None)
    }

    #[fixture]
    fn weighted_graph() -> (
        &'static str,
        PortGraph,
        Option<Hierarchy>,
        Option<Weights<String, String>>,
    ) {
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

        ("weighted", graph, None, Some(weights))
    }

    #[rstest]
    #[case::flat(flat_graph())]
    #[case::hierarchy(hierarchy_graph())]
    #[case::interregional(hierarchy_interregional_graph())]
    #[case::weighted(weighted_graph())]
    fn mermaid_output<WN: Display + Clone, WP>(
        #[case] graph_elems: (
            &str,
            impl MermaidFormat,
            Option<Hierarchy>,
            Option<Weights<WN, WP>>,
        ),
    ) {
        let (name, graph, hierarchy, weights) = graph_elems;
        let mermaid = match (hierarchy, weights) {
            (Some(h), Some(w)) => graph
                .mermaid_format()
                .with_hierarchy(&h)
                .with_weights(&w)
                .finish(),
            (Some(h), None) => graph.mermaid_format().with_hierarchy(&h).finish(),
            (None, Some(w)) => graph.mermaid_format().with_weights(&w).finish(),
            (None, None) => graph.mermaid_string(),
        };

        let name = format!("{}__mermaid", name);
        insta::assert_snapshot!(name, mermaid);
    }

    #[rstest]
    #[case::flat(flat_graph())]
    #[case::hierarchy(hierarchy_graph())]
    #[case::interregional(hierarchy_interregional_graph())]
    #[case::weighted(weighted_graph())]
    fn dot_output<WN: Display + Clone, WP: Display + Clone>(
        #[case] graph_elems: (
            &str,
            impl DotFormat,
            Option<Hierarchy>,
            Option<Weights<WN, WP>>,
        ),
    ) {
        let (name, graph, hierarchy, weights) = graph_elems;
        let dot = match (hierarchy, weights) {
            (Some(h), Some(w)) => graph
                .dot_format()
                .with_hierarchy(&h)
                .with_weights(&w)
                .finish(),
            (Some(h), None) => graph.dot_format().with_hierarchy(&h).finish(),
            (None, Some(w)) => graph.dot_format().with_weights(&w).finish(),
            (None, None) => graph.dot_string(),
        };

        let name = format!("{}__dot", name);
        insta::assert_snapshot!(name, dot);
    }
}
