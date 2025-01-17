use portgraph::{LinkMut, NodeIndex, PortGraph, PortIndex, PortMut, PortView};
use std::collections::HashMap;

use crate::{generator::GraphData, Operation};

#[derive(Debug, Clone)]
pub struct GraphBuilder {
    graph: PortGraph,
    weights: HashMap<NodeIndex, Operation>,
    last_ports: Vec<PortIndex>,
    width: usize,
}

impl GraphBuilder {
    pub fn new(width: usize) -> Self {
        let mut graph = PortGraph::new();
        let mut weights = HashMap::new();

        // Create input node with w output ports
        let input = graph.add_node(0, width);
        weights.insert(input, Operation::Input);

        // Initialize last_ports with input node's output ports
        let last_ports: Vec<PortIndex> = (0..width)
            .map(|i| graph.output(input, i).unwrap())
            .collect();

        Self {
            graph,
            weights,
            last_ports,
            width,
        }
    }

    pub fn n_operations(&self) -> usize {
        self.weights.len() - 1
    }

    pub fn add_operation(&mut self, op: Operation, i: usize, j: usize) {
        let node = self.graph.add_node(2, 2);
        self.weights.insert(node, op);

        // Connect to previous ports that used indices i and j
        let to_port = self.graph.input(node, 0).unwrap();
        self.graph.link_ports(self.last_ports[i], to_port).unwrap();

        let to_port = self.graph.input(node, 1).unwrap();
        self.graph.link_ports(self.last_ports[j], to_port).unwrap();

        // Update last port for both indices with this node's output
        self.last_ports[i] = self.graph.output(node, 0).unwrap();
        self.last_ports[j] = self.graph.output(node, 1).unwrap();
    }

    pub fn finish(mut self) -> GraphData {
        // Create output node and connect remaining ports
        let output = self.graph.add_node(self.width, 0);
        self.weights.insert(output, Operation::Output);

        for (i, port) in self.last_ports.iter().enumerate() {
            let to_port = self.graph.input(output, i).unwrap();
            self.graph.link_ports(*port, to_port).unwrap();
        }

        GraphData {
            graph: self.graph,
            weights: self.weights,
        }
    }
}
