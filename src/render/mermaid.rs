//! Functions to encode a `PortGraph` in mermaid format.

use std::fmt::Display;

use crate::{Hierarchy, LinkView, NodeIndex, Weights};

use super::{EdgeStyle, NodeStyle};

/// The indentation separator for the mermaid string.
///
/// This is purely cosmetic and does not affect the mermaid rendering.
const INDENTATION_SEPARATOR: &str = "    ";

/// Configurable mermaid formatter for a `PortGraph`.
///
/// Use the [`MermaidFormat`] trait to encode a `PortGraph` in mermaid format.
///
/// # Example
///
/// ```rust
/// # use portgraph::{LinkMut, PortGraph, PortMut, PortView, Hierarchy};
/// # use portgraph::render::MermaidFormat;
/// let mut graph = PortGraph::new();
/// let n1 = graph.add_node(3, 2);
/// let n2 = graph.add_node(0, 1);
/// let n3 = graph.add_node(1, 0);
/// graph.link_nodes(n2, 0, n3, 0).unwrap();
///
/// let mut hier = Hierarchy::new();
/// hier.push_child(n2, n1).unwrap();
/// hier.push_child(n3, n1).unwrap();
///
/// let mermaid = graph.mermaid_format().with_hierarchy(&hier).finish();
/// ```
pub struct MermaidFormatter<'g, G: LinkView> {
    graph: &'g G,
    forest: Option<&'g Hierarchy>,
    node_style: Option<Box<dyn FnMut(NodeIndex) -> NodeStyle + 'g>>,
    #[allow(clippy::type_complexity)]
    edge_style: Option<Box<dyn FnMut(G::LinkEndpoint, G::LinkEndpoint) -> EdgeStyle + 'g>>,
}

impl<'g, G> MermaidFormatter<'g, G>
where
    G: LinkView,
{
    /// Initialize a new `MermaidFormatter` for `graph`.
    pub fn new(graph: &'g G) -> Self {
        Self {
            graph,
            forest: None,
            node_style: None,
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

    /// Set the function to use to get the style of an edge.
    pub fn with_edge_style(
        mut self,
        edge_style: impl FnMut(G::LinkEndpoint, G::LinkEndpoint) -> EdgeStyle + 'g,
    ) -> Self {
        self.edge_style = Some(Box::new(edge_style));
        self
    }

    /// Encode some `Weights` in the mermaid format.
    ///
    /// This is a convenience method to set the node and port styles based on the weight values.
    /// It overrides any previous node or port style set.
    pub fn with_weights<'w, N, P>(self, weights: &'w Weights<N, P>) -> Self
    where
        'w: 'g,
        N: Display + Clone,
    {
        self.with_node_style(|n| NodeStyle::new(&weights.nodes[n]))
    }

    /// Encode the graph in mermaid format.
    pub fn finish(mut self) -> String {
        let mut mermaid = MermaidBuilder::init(self.node_style.take(), self.edge_style.take());

        // Explore the hierarchy from the root nodes, and add the nodes and edges to the mermaid definition.
        for root in self.graph.nodes_iter().filter(|n| self.is_root(*n)) {
            self.explore_node(&mut mermaid, root);
        }

        mermaid.finish()
    }

    /// Encode the nodes, starting from a set of roots.
    fn explore_node(&self, mmd: &mut MermaidBuilder<'g, G>, node: NodeIndex) {
        if self.is_leaf(node) {
            mmd.add_leaf(node);
        } else {
            mmd.start_subgraph(node);
            for child in self
                .forest
                .map_or_else(Vec::new, |f| f.children(node).collect())
            {
                self.explore_node(mmd, child);
            }
            mmd.end_subgraph();
        }
        for (src, tgt) in self.graph.output_links(node) {
            let src_node = self.graph.port_node(src).unwrap();
            let tgt_node = self.graph.port_node(tgt).unwrap();
            mmd.add_link(src_node, src, tgt_node, tgt);
        }
    }

    /// Helper function to check if a node is a leaf in the hierarchy.
    fn is_root(&self, node: NodeIndex) -> bool {
        self.forest.map_or(true, |f| f.is_root(node))
    }

    /// Helper function to check if a node is a leaf in the hierarchy.
    fn is_leaf(&self, node: NodeIndex) -> bool {
        self.forest.map_or(true, |f| !f.has_children(node))
    }
}

/// A trait for encoding a graph in mermaid format.
pub trait MermaidFormat: LinkView + Sized {
    /// Initialize a [`MermaidFormatter`] for the graph.
    ///
    /// Call [`MermaidFormatter::finish`] to produce the final mermaid string.
    ///
    /// Note that mermaid diagrams do not support ports, so graph edges may be
    /// unordered.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use portgraph::{LinkMut, PortGraph, PortMut, PortView, Hierarchy};
    /// # use portgraph::render::MermaidFormat;
    /// let mut graph = PortGraph::new();
    /// let n1 = graph.add_node(3, 2);
    /// let n2 = graph.add_node(0, 1);
    /// let n3 = graph.add_node(1, 0);
    /// graph.link_nodes(n2, 0, n3, 0).unwrap();
    ///
    /// let mut hier = Hierarchy::new();
    /// hier.push_child(n2, n1).unwrap();
    /// hier.push_child(n3, n1).unwrap();
    ///
    /// let mermaid = graph.mermaid_format().with_hierarchy(&hier).finish();
    /// ```
    ///
    /// results in
    ///
    /// ```mermaid
    /// graph LR
    ///     subgraph 0 [0]
    ///         direction LR
    ///         1[1]
    ///         1-->2
    ///         2[2]
    ///     end
    /// ```
    fn mermaid_format(&self) -> MermaidFormatter<'_, Self>;

    /// Encode the graph in mermaid format. See
    /// [`MermaidFormat::mermaid_format`] for more control over the output
    /// style.
    ///
    /// Note that mermaid diagrams do not support ports, so graph edges may be
    /// unordered.
    fn mermaid_string(&self) -> String {
        self.mermaid_format().finish()
    }
}

impl<G> MermaidFormat for G
where
    G: LinkView,
{
    fn mermaid_format(&self) -> MermaidFormatter<'_, Self> {
        MermaidFormatter::new(self)
    }
}

/// Helper struct to manage building a mermaid string.
///
/// Splitting this from the `MermaidFormatter` allows us to mutate this freely
/// while keeping references to the graph.
struct MermaidBuilder<'g, G: LinkView> {
    /// The mmd definition being built.
    output: String,
    /// The current indentation level.
    indent: usize,
    /// The styling function for nodes.
    node_style: Option<Box<dyn FnMut(NodeIndex) -> NodeStyle + 'g>>,
    /// The styling function for edges.
    #[allow(clippy::type_complexity)]
    edge_style: Option<Box<dyn FnMut(G::LinkEndpoint, G::LinkEndpoint) -> EdgeStyle + 'g>>,
}

impl<'g, G: LinkView> MermaidBuilder<'g, G> {
    /// Start a new flowchart definition.
    #[allow(clippy::type_complexity)]
    pub fn init(
        node_style: Option<Box<dyn FnMut(NodeIndex) -> NodeStyle + 'g>>,
        edge_style: Option<Box<dyn FnMut(G::LinkEndpoint, G::LinkEndpoint) -> EdgeStyle + 'g>>,
    ) -> Self {
        Self {
            output: "graph LR\n".to_string(),
            indent: 1,
            node_style,
            edge_style,
        }
    }

    /// Push an arbitrary line of text to the output.
    /// Indents the line according to the current indentation level.
    pub fn push_line(&mut self, s: impl AsRef<str>) {
        let extra_capacity = self.indent * INDENTATION_SEPARATOR.len() + s.as_ref().len() + 1;
        self.output.reserve(extra_capacity);

        self.output
            .push_str(&INDENTATION_SEPARATOR.repeat(self.indent));
        self.output.push_str(s.as_ref());
        self.output.push('\n');
    }

    /// Push an arbitrary line of text to the output.
    /// Indents the line according to the current indentation level.
    fn push_strings(&mut self, strings: &[&str]) {
        let extra_capacity = self.indent * INDENTATION_SEPARATOR.len()
            + strings.iter().map(|s| s.len()).sum::<usize>()
            + 1;
        self.output.reserve(extra_capacity);

        self.output
            .push_str(&INDENTATION_SEPARATOR.repeat(self.indent));
        for s in strings {
            self.output.push_str(s);
        }
        self.output.push('\n');
    }

    /// Adds a leaf node to the mermaid definition.
    pub fn add_leaf(&mut self, node: NodeIndex) {
        let style = self
            .node_style
            .as_mut()
            .map_or_else(NodeStyle::default, |f| f(node));
        let id = node.index().to_string();

        match style {
            NodeStyle::Hidden => self.push_strings(&[id.as_ref(), ":::hidden"]),
            NodeStyle::Box(lbl) => {
                self.push_strings(&[id.as_ref(), "[", &encode_label(&id, &lbl), "]"])
            }
        }
    }

    /// Start a new subgraph block.
    /// Call `end_subgraph` to close the block.
    ///
    /// Blocks may be nested.
    pub fn start_subgraph(&mut self, node: NodeIndex) {
        let style = self
            .node_style
            .as_mut()
            .map_or_else(NodeStyle::default, |f| f(node));
        let id = node.index().to_string();

        match style {
            NodeStyle::Hidden => self.push_strings(&["subgraph ", id.as_ref(), " [ ]"]),
            NodeStyle::Box(lbl) => self.push_strings(&[
                "subgraph ",
                id.as_ref(),
                " [",
                &encode_label(&id, &lbl),
                "]",
            ]),
        }
        self.indent += 1;
        self.push_line("direction LR");
    }

    /// End the current indented block.
    pub fn end_subgraph(&mut self) {
        self.indent -= 1;
        self.push_line("end");
    }

    /// Adds an edge to the mermaid definition.
    pub fn add_link(
        &mut self,
        src_node: NodeIndex,
        src: G::LinkEndpoint,
        tgt_node: NodeIndex,
        tgt: G::LinkEndpoint,
    ) {
        let style = self
            .edge_style
            .as_mut()
            .map_or_else(EdgeStyle::default, |f| f(src, tgt));
        let src = src_node.index().to_string();
        let tgt = tgt_node.index().to_string();
        self.push_strings(&[&src, &style.as_mermaid_str(), &tgt]);
    }

    /// Returns the built mermaid definition.
    pub fn finish(self) -> String {
        self.output
    }
}

/// Encode a label, or use the id if the label is empty.
///
/// We escape double quotes and newlines in the label.
/// Other special characters may need escaping by the user.
///
/// See https://mermaid.js.org/syntax/flowchart.html#special-characters-that-break-syntax.
pub fn encode_label(id: &str, label: &str) -> String {
    if label.is_empty() {
        return id.to_string();
    }
    format!("\"{}\"", label.replace('"', "#quot;").replace('\n', "<br>"))
}
