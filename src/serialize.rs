//! Serialization definition for a composition of [`PortGraph`] and
//! [`Hierarchy`] ([`HierGraph`]).
//! [`PortGraph`]: crate::portgraph::PortGraph
//! [`Hierarchy`]: crate::hierarchy::Hierarchy

use crate::{Direction, Hierarchy, NodeIndex, PortGraph, PortIndex};
use serde::{Deserialize, Deserializer, Serialize};

/**
Compound of [`PortGraph`] and [`Hierarchy`] that allows more erganomic serialization.

Implements serde::{Deserialize, Serialize}
Serializes to list of nodes and list of edges,
with nodes defined by a tuple of (optional parent pointer, number of inputs,
number of outputs), and edges by tuple of ((source node, offset),
(target_node, offset)).
Note if the nodes are not compact (no free nodes), serialization will fail.

[`PortGraph`]: crate::portgraph::PortGraph
[`Hierarchy`]: crate::hierarchy::Hierarchy
*/
#[derive(Default, PartialEq, Debug)]
pub struct HierGraph {
    /// Underlying [`PortGraph`]
    pub graph: PortGraph,
    /// Underlying [`Hierarchy`]
    pub hier: Hierarchy,
}

#[derive(Serialize, Deserialize)]
struct SerHierGraph {
    nodes: Vec<(Option<usize>, usize, usize)>,
    edges: Vec<[[usize; 2]; 2]>,
}

impl From<&HierGraph> for SerHierGraph {
    fn from(HierGraph { graph, hier }: &HierGraph) -> Self {
        let nodes: Vec<_> = graph
            .nodes_iter()
            .enumerate()
            .map(|(i, n)| {
                assert_eq!(i, n.index(), "can't serialize a non-compact graph");
                let parent = hier.parent(n);

                (
                    parent.map(NodeIndex::index),
                    graph.num_inputs(n),
                    graph.num_outputs(n),
                )
            })
            .collect();

        let find_offset = |p: PortIndex| {
            [
                graph.port_node(p).unwrap().index(),
                graph.port_offset(p).unwrap().index(),
            ]
        };
        let edges: Vec<_> = graph
            .ports_iter()
            .filter_map(|p| {
                if graph.port_direction(p) == Some(Direction::Outgoing) {
                    let tgt = graph.port_link(p)?;
                    Some([p, tgt].map(find_offset))
                } else {
                    None
                }
            })
            .collect();

        Self { nodes, edges }
    }
}

impl From<SerHierGraph> for HierGraph {
    fn from(SerHierGraph { nodes, edges }: SerHierGraph) -> Self {
        let mut hier = Hierarchy::new();

        // if there are any unconnected ports the capacity will be an
        // underestimate
        let mut graph = PortGraph::with_capacity(nodes.len(), edges.len() * 2);
        for (parent, incoming, outgoing) in nodes {
            let ni = graph.add_node(incoming, outgoing);
            if let Some(parent) = parent {
                hier.push_child(ni, NodeIndex::new(parent))
                    .expect("Unexpected hierarchy error"); // TODO remove unwrap
            }
        }

        for [[srcn, from_offset], [tgtn, to_offset]] in edges {
            graph
                .link_nodes(
                    NodeIndex::new(srcn),
                    from_offset,
                    NodeIndex::new(tgtn),
                    to_offset,
                )
                .expect("Unexpected link error");
        }

        Self { graph, hier }
    }
}

impl Serialize for HierGraph {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let shg: SerHierGraph = self.into();
        shg.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for HierGraph {
    fn deserialize<D>(deserializer: D) -> Result<HierGraph, D::Error>
    where
        D: Deserializer<'de>,
    {
        let shg = SerHierGraph::deserialize(deserializer)?;
        Ok(shg.into())
    }
}

#[cfg(test)]
#[cfg(feature = "proptest")]
pub mod test {
    use std::io::Write;

    use super::*;
    use crate::proptest::gen_portgraph;
    use proptest::prelude::*;
    proptest! {
        #[test]
        fn prop_serialization(mut graph in gen_portgraph(100, 50, 1000)) {
            let root = graph.add_node(0, 0);
            let mut hier = Hierarchy::new();
            for n in graph.nodes_iter() {
                if n != root {
                    hier.push_child(n, root).unwrap();
                }
            }

            let hgraph = HierGraph { graph, hier};

            prop_assert_eq!(ser_roundtrip(&hgraph), hgraph);
        }
    }

    #[test]
    fn empty_portgraph_serialize() {
        // let g = PortGraph::new();
        let hg = HierGraph::default();
        assert_eq!(ser_roundtrip(&hg), hg);
    }
    pub fn ser_roundtrip<T: Serialize + serde::de::DeserializeOwned>(g: &T) -> T {
        let v = rmp_serde::to_vec_named(g).unwrap();
        rmp_serde::from_slice(&v[..]).unwrap()
    }

    #[test]
    fn simpleser() {
        let mut g = PortGraph::new();
        let a = g.add_node(1, 1);
        let b = g.add_node(3, 2);
        let c = g.add_node(1, 1);
        let root = g.add_node(0, 0);

        g.link_nodes(a, 0, b, 0).unwrap();
        g.link_nodes(b, 0, b, 1).unwrap();
        g.link_nodes(b, 1, c, 0).unwrap();
        g.link_nodes(c, 0, a, 0).unwrap();

        let mut h = Hierarchy::new();

        for n in [a, b, c] {
            h.push_child(n, root).unwrap();
        }
        let hg = HierGraph { graph: g, hier: h };
        let v = rmp_serde::to_vec_named(&hg).unwrap();
        use std::fs::File;
        let mut b = File::create("foo.bin").unwrap();
        b.write(&v[..]).unwrap();
        let newhg = rmp_serde::from_slice(&v[..]).unwrap();
        assert_eq!(hg, newhg);
    }
}
