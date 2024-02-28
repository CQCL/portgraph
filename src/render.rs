//! This module contains rendering logic from portgraphs into graphviz and
//! mermaid diagrams.

mod dot;
mod mermaid;

use std::borrow::Cow;

pub use dot::{DotFormat, DotFormatter};
pub use mermaid::{MermaidFormat, MermaidFormatter};

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
    /// Custom style
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
            Self::Labelled(lbl, e) => match e.as_ref() {
                Self::Solid => format!("--{}-->", lbl).into(),
                Self::Dotted => format!("-.{}.-", lbl).into(),
                Self::Dashed => format!("-.{}.-", lbl).into(),
                Self::Custom(s) => s.into(),
                Self::Labelled(_, _) => panic!("Nested labelled edges are not supported"),
            },
        }
    }
}
