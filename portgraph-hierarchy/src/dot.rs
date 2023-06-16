//! Functions to encode a `PortGraph` in dot format.

use std::collections::VecDeque;

use portgraph::NodeIndex;

use crate::Hierarchy;

impl Hierarchy {
    /// Returns a dot graph representation of the hierarchy.
    pub fn dot_string(&self, root: NodeIndex) -> String {
        let mut dot = String::new();
        dot.push_str("digraph {\n");
        self.hierarchy_string(root, &mut dot);
        dot.push_str("}\n");
        dot
    }

    /// Returns a dot graph representation of the hierarchy as a subgraph element.
    ///
    /// The resulting string can be included in a larger graph definition.
    pub fn dot_string_subgraph(&self, root: NodeIndex) -> String {
        let mut dot = String::new();
        dot.push_str("digraph {\n");
        self.hierarchy_string(root, &mut dot);
        dot.push_str("}\n");
        dot
    }

    fn hierarchy_string(&self, root: NodeIndex, dot: &mut String) {
        let hier_node_id = |n: NodeIndex| format!("hier{}", n.index());

        let mut queue = VecDeque::from([root]);
        while let Some(n) = queue.pop_front() {
            let node_str = format!(
                "{} [shape=plain label=\"{}\"]\n",
                hier_node_id(n),
                n.index()
            );
            dot.push_str(&node_str);

            // Connect the parent to any existing children
            self.children(n).for_each(|child| {
                dot.push_str(&{
                    let from_node = n;
                    let to_node = child;
                    format!(
                        "{} -> {}  [style = \"dashed\"] \n",
                        hier_node_id(from_node),
                        hier_node_id(to_node),
                    )
                });
                queue.push_back(child);
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hier_dot_string() {
        let mut hier = Hierarchy::new();
        let n1 = NodeIndex::new(0);
        let n2 = NodeIndex::new(1);
        let n3 = NodeIndex::new(2);

        hier.push_child(n2, n1).unwrap();
        hier.push_child(n3, n1).unwrap();
        let dot = hier.dot_string(n1);
        let expected = r#"digraph {
hier0 [shape=plain label="0"]
hier0 -> hier1  [style = "dashed"] 
hier0 -> hier2  [style = "dashed"] 
hier1 [shape=plain label="1"]
hier2 [shape=plain label="2"]
}
"#;
        assert_eq!(dot, expected, "\n{}\n{}\n", dot, expected);
    }
}
