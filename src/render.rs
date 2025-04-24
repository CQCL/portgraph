//! This module contains rendering logic from portgraphs into graphviz and
//! mermaid diagrams.

mod dot;
mod mermaid;

use std::borrow::Cow;

pub use dot::{DotFormat, DotFormatter};
pub use mermaid::{MermaidFormat, MermaidFormatter};

use self::mermaid::encode_label;

/// Presentation attributes of a rendered element
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct PresentationStyle {
    /// Main color of the element.
    ///
    /// Encoded as an RGB hex string.
    /// E.g. `#f00`, `#AE00FF`.
    pub color: Option<String>,
    /// Background fill color.
    ///
    /// Encoded as an RGB hex string.
    /// E.g. `#f00`, `#AE00FF`.
    pub fill: Option<String>,
    /// Stroke color.
    ///
    /// Encoded as an RGB hex string.
    /// E.g. `#ff0000`, `#AE00FF`.
    pub stroke: Option<String>,
    /// Stroke width.
    ///
    /// Encoded as pixels or a similar unit.
    /// E.g. `1px`, `2pt`, `0.5em`.
    pub stroke_width: Option<String>,
}

impl PresentationStyle {
    /// Returns a new presentation style with no attributes set.
    pub const fn new() -> Self {
        Self {
            color: None,
            fill: None,
            stroke: None,
            stroke_width: None,
        }
    }

    /// Returns `true` if the presentation style is empty.
    pub const fn is_empty(&self) -> bool {
        self.color.is_none()
            && self.fill.is_none()
            && self.stroke.is_none()
            && self.stroke_width.is_none()
    }
}

/// Style of a rendered node.
///
/// Defaults to a box with no label.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum NodeStyle {
    /// Ignore the node. No edges will be connected to it.
    Hidden,
    /// Draw a box with the label inside.
    #[deprecated(since = "0.14.1", note = "Use `Box` instead")]
    Box(String),
    /// Draw a box with label inside.
    #[non_exhaustive]
    Boxed {
        /// Label of the node.
        label: String,
        /// Additional presentation attributes.
        attrs: PresentationStyle,
    },
}

impl NodeStyle {
    /// Show a node label with the default style.
    #[deprecated(since = "0.14.1", note = "Use `boxed` instead")]
    pub fn new(label: impl ToString) -> Self {
        Self::Boxed {
            label: label.to_string(),
            attrs: Default::default(),
        }
    }

    /// Show a node in a box.
    ///
    /// Additional presentation attributes can be set using [`NodeStyle::with_attrs`].
    pub fn boxed(label: impl ToString) -> Self {
        Self::Boxed {
            label: label.to_string(),
            attrs: Default::default(),
        }
    }

    /// Set the presentation attributes of the node.
    pub fn with_attrs(mut self, attrs: PresentationStyle) -> Self {
        if let Self::Boxed { attrs: a, .. } = &mut self {
            *a = attrs
        }
        self
    }

    /// Returns the presentation attributes of the node.
    pub fn attrs(&self) -> &PresentationStyle {
        static DEFAULT: PresentationStyle = PresentationStyle::new();
        match self {
            Self::Boxed { attrs, .. } => attrs,
            _ => &DEFAULT,
        }
    }
}

impl Default for NodeStyle {
    fn default() -> Self {
        Self::Boxed {
            label: String::new(),
            attrs: Default::default(),
        }
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
#[allow(clippy::type_complexity)]
mod test {
    use std::fmt::Display;
    use std::sync::OnceLock;

    use rstest::{fixture, rstest};

    use crate::view::Region;
    use crate::{Hierarchy, LinkMut, NodeIndex, PortGraph, PortMut, PortView, Weights};

    use super::{DotFormat, MermaidFormat, NodeStyle, PresentationStyle};

    /// A simple flat graph with some nodes and edges.
    #[fixture]
    fn flat_graph() -> (
        &'static str,
        PortGraph,
        Option<Hierarchy>,
        Option<Weights<String, String>>,
        Option<fn(NodeIndex) -> NodeStyle>,
    ) {
        let mut graph = PortGraph::new();
        let n1 = graph.add_node(3, 2);
        let n2 = graph.add_node(1, 0);
        let n3 = graph.add_node(1, 0);
        graph.link_nodes(n1, 0, n2, 0).unwrap();
        graph.link_nodes(n1, 1, n3, 0).unwrap();
        ("flat", graph, None, None, None)
    }

    #[fixture]
    fn hierarchy_graph() -> (
        &'static str,
        PortGraph,
        Option<Hierarchy>,
        Option<Weights<String, String>>,
        Option<impl FnMut(NodeIndex) -> NodeStyle>,
    ) {
        let mut graph = PortGraph::new();
        let n1 = graph.add_node(3, 2);
        let n2 = graph.add_node(0, 1);
        let n3 = graph.add_node(1, 0);
        graph.link_nodes(n2, 0, n3, 0).unwrap();

        let mut hier = Hierarchy::new();
        hier.push_child(n2, n1).unwrap();
        hier.push_child(n3, n1).unwrap();

        let node_style = move |n: NodeIndex| {
            if n == n1 {
                NodeStyle::boxed("root").with_attrs(PresentationStyle {
                    color: Some("#f00".to_string()),
                    fill: Some("#0f0".to_string()),
                    stroke: Some("#00f".to_string()),
                    stroke_width: Some("4px".to_string()),
                })
            } else {
                NodeStyle::boxed(n.index())
            }
        };

        ("hierarchy", graph, Some(hier), None, Some(node_style))
    }

    /// A hierarchical graph with edges between different regions.
    #[fixture]
    fn hierarchy_interregional_graph() -> (
        &'static str,
        PortGraph,
        Option<Hierarchy>,
        Option<Weights<String, String>>,
        Option<fn(NodeIndex) -> NodeStyle>,
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

        ("hierarchy_interregional", graph, Some(hier), None, None)
    }

    #[fixture]
    fn weighted_graph() -> (
        &'static str,
        PortGraph,
        Option<Hierarchy>,
        Option<Weights<String, String>>,
        Option<fn(NodeIndex) -> NodeStyle>,
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

        ("weighted", graph, None, Some(weights), None)
    }

    #[allow(clippy::type_complexity)]
    #[fixture]
    fn region_view() -> (
        &'static str,
        Region<'static, PortGraph>,
        Option<Hierarchy>,
        Option<Weights<String, String>>,
        Option<fn(NodeIndex) -> NodeStyle>,
    ) {
        let mut graph = PortGraph::new();
        let other = graph.add_node(42, 0);
        let root = graph.add_node(1, 0);
        let a = graph.add_node(1, 2);
        let b = graph.add_node(0, 0);
        let c = graph.add_node(0, 0);
        graph.link_nodes(a, 0, other, 0).unwrap();
        graph.link_nodes(a, 1, root, 0).unwrap();

        static HIERARCHY: OnceLock<Hierarchy> = OnceLock::new();
        let hierarchy = HIERARCHY.get_or_init(|| {
            let mut hierarchy = Hierarchy::new();
            hierarchy.push_child(root, other).unwrap();
            hierarchy.push_child(a, root).unwrap();
            hierarchy.push_child(b, root).unwrap();
            hierarchy.push_child(c, b).unwrap();
            hierarchy
        });

        let region = Region::new(graph, hierarchy, root);

        ("region_view", region, Some(hierarchy.clone()), None, None)
    }

    #[rstest]
    #[case::flat(flat_graph())]
    #[case::hierarchy(hierarchy_graph())]
    #[case::interregional(hierarchy_interregional_graph())]
    #[case::weighted(weighted_graph())]
    #[case::region_view(region_view())]
    #[cfg_attr(miri, ignore)] // Opening files is not supported in (isolated) miri
    fn mermaid_output<WN: Display + Clone, WP>(
        #[case] graph_elems: (
            &str,
            impl MermaidFormat,
            Option<Hierarchy>,
            Option<Weights<WN, WP>>,
            Option<impl FnMut(NodeIndex) -> NodeStyle>,
        ),
    ) {
        let (name, graph, hierarchy, weights, node_style) = graph_elems;

        let fmt = graph.mermaid_format();
        let fmt = match &hierarchy {
            Some(h) => fmt.with_hierarchy(h),
            None => fmt,
        };
        let fmt = match node_style {
            Some(node_style) => fmt.with_node_style(node_style),
            None => fmt,
        };
        let fmt = match &weights {
            Some(w) => fmt.with_weights(w),
            None => fmt,
        };
        let mermaid = fmt.finish();

        let name = format!("{}__mermaid", name);
        insta::assert_snapshot!(name, mermaid);
    }

    #[rstest]
    #[case::flat(flat_graph())]
    #[case::hierarchy(hierarchy_graph())]
    #[case::interregional(hierarchy_interregional_graph())]
    #[case::weighted(weighted_graph())]
    #[cfg_attr(miri, ignore)] // Opening files is not supported in (isolated) miri
    fn dot_output<WN: Display + Clone, WP: Display + Clone>(
        #[case] graph_elems: (
            &str,
            impl DotFormat,
            Option<Hierarchy>,
            Option<Weights<WN, WP>>,
            Option<impl FnMut(NodeIndex) -> NodeStyle>,
        ),
    ) {
        let (name, graph, hierarchy, weights, node_style) = graph_elems;

        let fmt = graph.dot_format();
        let fmt = match &hierarchy {
            Some(h) => fmt.with_hierarchy(h),
            None => fmt,
        };
        let fmt = match node_style {
            Some(node_style) => fmt.with_node_style(node_style),
            None => fmt,
        };
        let fmt = match &weights {
            Some(w) => fmt.with_weights(w),
            None => fmt,
        };
        let dot = fmt.finish();

        let name = format!("{}__dot", name);
        insta::assert_snapshot!(name, dot);
    }
}
