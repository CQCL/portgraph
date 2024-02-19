//! Strategies for property testing using the `proptest` crate
//!
//! Currently, this module exposes a single function [`gen_portgraph`], which
//! returns strategies that generate random portgraphs.
use std::collections::{BTreeMap, HashSet};

use crate::{LinkMut, MultiPortGraph, NodeIndex, PortGraph, PortMut, PortOffset, PortView};
use proptest::prelude::*;

#[derive(Debug, Clone, Copy)]
struct Edge {
    src_v: NodeIndex,
    target_v: NodeIndex,
    src_p: PortOffset,
    target_p: PortOffset,
}
prop_compose! {
    /// A random set of edges for a portgraph.
    fn gen_edges(max_n_nodes: usize, max_n_ports: usize, max_n_edges: usize)(
        n_edges in 0..=max_n_edges
    )(
        out_ports in vec![(1..max_n_nodes, 0..max_n_ports); n_edges],
        in_ports in vec![(1..max_n_nodes, 0..max_n_ports); n_edges],
    ) -> Vec<Edge> {
        out_ports.into_iter().zip(in_ports).map(|((src_v, src_p), (target_v, target_p))| {
            Edge {
                src_v: NodeIndex::new(src_v),
                target_v: NodeIndex::new(target_v),
                src_p: PortOffset::new_outgoing(src_p),
                target_p: PortOffset::new_incoming(target_p),
            }
        }).collect()
    }
}

prop_compose! {
    /// A random set of distinct edges for a portgraph.
    fn gen_unique_edges(max_n_nodes: usize, max_n_ports: usize, max_n_edges: usize)(
        out_ports in prop::collection::hash_set((1..max_n_nodes, 0..max_n_ports), 0..=max_n_edges),
        in_ports in prop::collection::hash_set((1..max_n_nodes, 0..max_n_ports), 0..=max_n_edges),
    ) -> Vec<Edge> {
        // Unlike the non-unique case, in this case we do not "control" the number of
        // edges directly. Might make shrinking slightly more difficult.
        out_ports.into_iter().zip(in_ports).map(|((src_v, src_p), (target_v, target_p))| {
            Edge {
                src_v: NodeIndex::new(src_v),
                target_v: NodeIndex::new(target_v),
                src_p: PortOffset::new_outgoing(src_p),
                target_p: PortOffset::new_incoming(target_p),
            }
        }).collect()
    }
}

prop_compose! {
    /// A random non-empty portgraph
    ///
    /// With at least 1 and at most `max_n_nodes` nodes, with at most `max_port`
    /// incoming and outgoing ports at ever node, and at most `max_n_edges`.
    pub fn gen_portgraph(max_n_nodes: usize, max_n_ports: usize, max_n_edges: usize)(
        edges in gen_unique_edges(max_n_nodes, max_n_ports, max_n_edges)
    ) -> PortGraph {
        let mut g: PortGraph = graph_from_edges(&edges);
        ensure_non_empty(&mut g);
        g
    }
}

prop_compose! {
    /// A random non-empty multiportgraph
    ///
    /// With at least 1 and at most `max_n_nodes` nodes, with at most `max_port`
    /// incoming and outgoing ports at ever node, and at most `max_n_edges`.
    pub fn gen_multiportgraph(max_n_nodes: usize, max_n_ports: usize, max_n_edges: usize)(
        edges in gen_edges(max_n_nodes, max_n_ports, max_n_edges)
    ) -> MultiPortGraph {
        let mut g: MultiPortGraph = graph_from_edges(&edges);
        ensure_non_empty(&mut g);
        g
    }
}

/// Pick a random node in portgraph g
///
/// Returns a tuple (g, node) so that strategies for portgraph generation can
/// be composed with this function. E.g, use as follows:
///
/// ```
/// use proptest::prelude::*;
///
/// proptest! {
///     #[test]
///     fn prop_test((g, n) in gen_node_index(gen_portgraph(10, 4, 20))) {
///         prop_assert!(true)
///     }
/// }
/// ```
pub fn gen_node_index<G>(g: G) -> impl Strategy<Value = (PortGraph, NodeIndex)>
where
    G: Strategy<Value = PortGraph>,
{
    g.prop_flat_map(move |g| {
        let node_count = g.node_count();
        let nodes: Vec<_> = g.nodes_iter().collect();
        (Just(g), (0..node_count).prop_map(move |i| nodes[i]))
    })
}

fn graph_from_edges<G: PortMut + LinkMut + Default>(edges: &[Edge]) -> G {
    let mut map_vertices = BTreeMap::new();
    let mut in_port_counts = BTreeMap::new();
    let mut out_port_counts = BTreeMap::new();
    let mut add_port = |v, p| {
        let (max, port) = match p {
            PortOffset::Incoming(p) => (in_port_counts.entry(v).or_insert(0), p),
            PortOffset::Outgoing(p) => (out_port_counts.entry(v).or_insert(0), p),
        };
        *max = (*max).max(port as usize + 1);
    };
    for &Edge {
        src_v,
        target_v,
        src_p,
        target_p,
    } in edges
    {
        add_port(src_v, src_p);
        add_port(target_v, target_p);
    }
    let mut g = G::default();
    let vertices: HashSet<_> = edges
        .iter()
        .flat_map(|e| vec![e.src_v, e.target_v])
        .collect();
    for v in vertices {
        let in_ports = in_port_counts.get(&v).copied().unwrap_or(0);
        let out_ports = out_port_counts.get(&v).copied().unwrap_or(0);
        let new_v = g.add_node(in_ports, out_ports);
        map_vertices.insert(v, new_v);
    }
    for &Edge {
        src_v,
        target_v,
        src_p,
        target_p,
    } in edges
    {
        let src_v = map_vertices[&src_v];
        let target_v = map_vertices[&target_v];
        g.link_offsets(src_v, src_p, target_v, target_p).unwrap();
    }
    g
}

/// Parameters for random portgraph generation using proptest
#[derive(Debug, Clone)]
pub struct GenPortGraphParams {
    /// Maximum number of nodes in the graph.
    pub max_n_nodes: usize,
    /// Maximum number of incoming and outgoing ports per node.
    ///
    /// The maximum applies to incoming and outgoing ports separately. The total
    /// maximum number of ports per node is `2 * max_n_ports`.
    pub max_n_ports: usize,
    /// Maximum number of edges in the graph.
    pub max_n_edges: usize,
}

impl Default for GenPortGraphParams {
    fn default() -> Self {
        Self {
            max_n_nodes: 100,
            max_n_ports: 4,
            max_n_edges: 200,
        }
    }
}

impl Arbitrary for PortGraph {
    type Parameters = GenPortGraphParams;
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        gen_portgraph(args.max_n_nodes, args.max_n_ports, args.max_n_edges).boxed()
    }
}

impl Arbitrary for MultiPortGraph {
    type Parameters = GenPortGraphParams;
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        gen_multiportgraph(args.max_n_nodes, args.max_n_ports, args.max_n_edges).boxed()
    }
}

fn ensure_non_empty<G: PortView + PortMut>(g: &mut G) {
    if g.node_count() == 0 {
        g.add_node(0, 0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::LinkView;

    proptest! {
        #[test]
        fn gen_basic_graphs(graph in gen_portgraph(10, 4, 20)) {
            prop_assert!(graph.node_count() <= 10);
            prop_assert!(graph.node_count() >= 1);
            prop_assert!(graph.link_count() <= 20);
            prop_assert!(graph.port_count() <= 4 * 2 * graph.node_count());
        }
    }

    proptest! {
        #[test]
        fn gen_basic_multigraphs(graph in gen_multiportgraph(10, 4, 20)) {
            prop_assert!(graph.node_count() <= 10);
            prop_assert!(graph.node_count() >= 1);
            prop_assert!(graph.link_count() <= 20);
            prop_assert!(graph.port_count() <= 4 * 2 * graph.node_count());
        }
    }
}
