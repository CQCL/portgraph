//! Benchmark graph generators.

use portgraph::{Hierarchy, LinkMut, NodeIndex, PortGraph, PortMut, PortView, Weights};

/// Create line graph, connected with two parallel edges at each step.
///
/// o -2-> o -2-> o -2-> o -2-> o   ...
///
pub fn make_line_graph(size: usize) -> PortGraph {
    let mut graph = PortGraph::with_capacity(size, size * 2);
    let mut prev_node = graph.add_node(0, 2);

    for _ in 1..size {
        let new_node = graph.add_node(2, 2);
        graph.link_nodes(prev_node, 0, new_node, 0).unwrap();
        graph.link_nodes(prev_node, 1, new_node, 1).unwrap();
        prev_node = new_node;
    }

    graph
}

/// Create an acyclic graph with `layer` layers and 2 nodes per layer, connected sequentially as follows.
///
/// o ---> o ---> o ---> o ---> o   ...
/// |                    |
/// v                    v
/// o ---> o ---> o ---> o ---> o   ...
///
pub fn make_two_track_dag(layers: usize) -> PortGraph {
    let mut graph = PortGraph::with_capacity(2 * layers, 6 * layers);
    if layers == 0 {
        return graph;
    } else if layers == 1 {
        graph.add_node(1, 1);
        graph.add_node(1, 1);
        return graph;
    }

    let mut prev_nodes = [graph.add_node(1, 1), graph.add_node(1, 1)];

    for layer in 1..layers {
        let new_nodes = [graph.add_node(1, 2), graph.add_node(2, 1)];
        graph.link_nodes(prev_nodes[0], 0, new_nodes[0], 0).unwrap();
        graph.link_nodes(prev_nodes[1], 0, new_nodes[1], 0).unwrap();
        // Add an edge connecting both nodes every third layer
        if layer % 3 == 0 {
            graph.link_nodes(new_nodes[0], 1, new_nodes[1], 1).unwrap();
        }
        prev_nodes = new_nodes;
    }

    graph
}

/// Creates arbitrary weights for the nodes and ports of a graph.
pub fn make_weights(graph: &PortGraph) -> Weights<usize, isize> {
    let mut weights = Weights::with_capacity(graph.node_count(), graph.port_count());

    for (i, node) in graph.nodes_iter().enumerate() {
        weights[node] = i;
    }
    for (i, port) in graph.ports_iter().enumerate() {
        weights[port] = -(i as isize);
    }

    weights
}

/// Creates an arbitrary hierarchy for the nodes of a graph.
///
/// Uses a binary heap structure to assign parents to nodes.
/// The node `0` is the root of the hierarchy, and each node `i` has `2i + 1` and `2i + 2` as its children (if they exist).
pub fn make_hierarchy(graph: &PortGraph) -> Hierarchy {
    let mut hierarchy = Hierarchy::with_capacity(graph.node_count());
    for i in 1..graph.node_count() {
        let parent = Node::node_from_usize((i - 1) / 2);
        hierarchy.push_child(Node::node_from_usize(i), parent).unwrap();
    }
    hierarchy
}
