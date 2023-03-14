//! Strategies for property testing using the `proptest` crate
//!
//! Currently, this module exposes a single function [`gen_portgraph`], which
//! returns strategies that generate random portgraphs.
use std::iter::zip;

use crate::{Direction, PortGraph, PortIndex};
use proptest::prelude::*;
use rand::seq::SliceRandom;

prop_compose! {
    /// A random graph with random number of ports but no edges
    ///
    /// The graph has at least one node.
    ///
    ///  - `max_n_nodes` is the maximum number of nodes in the generated graph
    ///  - `max_port` is the maximum number of incoming and outgoing ports at
    ///    every node
    fn gen_no_edge_graph(max_n_nodes: usize, max_port: usize)(
        ports in prop::collection::vec(0..=max_port, 2..=2*max_n_nodes)
    ) -> PortGraph {
        let mut g = PortGraph::new();
        for ind in (0..ports.len() - 1).step_by(2) {
            g.add_node(ports[ind], ports[ind + 1]);
        }
        g
    }
}

/// A random graph and random edge lists
///
/// Returns a tuple of
///  - `graph`, a graph with ports but without edges
///  - `in_ports`, a list of incoming ports
///  - `out_port`, a list of outgoing ports, of the same length as `in_ports`
fn gen_graph_and_edges(
    max_n_nodes: usize,
    max_port: usize,
    max_n_edges: usize,
) -> impl Strategy<Value = (Vec<PortIndex>, Vec<PortIndex>, PortGraph)> {
    let graph = gen_no_edge_graph(max_n_nodes, max_port);
    (0..=max_n_edges, graph).prop_perturb(|(mut n_edges, graph), mut rng| {
        let (mut in_ports, mut out_ports): (Vec<_>, Vec<_>) = graph
            .ports_iter()
            .partition(|p| graph.port_direction(*p).unwrap() == Direction::Incoming);
        in_ports.shuffle(&mut rng);
        out_ports.shuffle(&mut rng);

        n_edges = [n_edges, in_ports.len(), out_ports.len()]
            .into_iter()
            .min()
            .unwrap();
        in_ports.truncate(n_edges);
        out_ports.truncate(n_edges);
        (in_ports, out_ports, graph)
    })
}

prop_compose! {
    /// A random non-empty portgraph
    ///
    /// With at least 1 and at most `max_n_nodes` nodes, with at most `max_port`
    /// incoming and outgoing ports at ever node, and at most `max_n_edges`.
    pub fn gen_portgraph(max_n_nodes: usize, max_port: usize, max_n_edges: usize)(
        (in_stubs, out_stubs, mut graph) in gen_graph_and_edges(max_n_nodes, max_port, max_n_edges)
    ) -> PortGraph {
        for (incoming, outgoing) in zip(in_stubs, out_stubs) {
            graph.link_ports(outgoing, incoming).unwrap();
        }
        graph
    }
}

#[cfg(test)]
mod tests {
    use super::gen_portgraph;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn gen_basic_graphs(graph in gen_portgraph(10, 4, 20)) {
            prop_assert!(graph.node_count() <= 10);
            prop_assert!(graph.node_count() >= 1);
            prop_assert!(graph.link_count() <= 20);
            prop_assert!(graph.port_count() <= 4 * 2 * graph.node_count());
        }
    }
}