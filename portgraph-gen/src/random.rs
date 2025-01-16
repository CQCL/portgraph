use crate::{
    generator::{GraphData, GraphGenerator},
    Operation,
};
use portgraph::{LinkMut, NodeIndex, PortGraph, PortIndex, PortMut, PortView};
use rand::prelude::*;

pub struct RandomGenerator {
    rng: StdRng,
}

impl RandomGenerator {
    pub fn new(seed: u64) -> Self {
        Self {
            rng: StdRng::seed_from_u64(seed),
        }
    }

    fn generate_operation(&mut self, width: usize) -> (Operation, usize, usize) {
        let i = self.rng.gen_range(0..width);
        let mut j = self.rng.gen_range(0..width);
        while j == i {
            j = self.rng.gen_range(0..width);
        }
        (Operation::random(&mut self.rng), i, j)
    }

    fn generate_single(&mut self, width: usize, depth: usize) -> GraphData {
        let mut graph = PortGraph::new();
        let mut weights = std::collections::HashMap::new();

        // Create input node with w output ports
        let input = graph.add_node(0, width);
        weights.insert(input, Operation::Input);

        // Create output node with w input ports
        let output = graph.add_node(width, 0);
        weights.insert(output, Operation::Output);

        // Generate operations and their indices
        let operations: Vec<(Operation, usize, usize)> =
            (0..depth).map(|_| self.generate_operation(width)).collect();

        // Keep track of last port that was used for each index
        let mut last_ports: Vec<PortIndex> = (0..width)
            .map(|i| graph.output(input, i).unwrap())
            .collect();
        let mut op_nodes = Vec::with_capacity(width);

        // Add operation nodes and connect them
        for (op, i, j) in operations {
            let node = graph.add_node(2, 2);
            weights.insert(node, op);
            op_nodes.push(node);

            // Connect to previous ports that used indices i and j
            let to_port = graph.input(node, 0).unwrap();
            graph.link_ports(last_ports[i], to_port).unwrap();

            let to_port = graph.input(node, 1).unwrap();
            graph.link_ports(last_ports[j], to_port).unwrap();

            // Update last port for both indices with this node's output
            last_ports[i] = graph.output(node, 0).unwrap();
            last_ports[j] = graph.output(node, 1).unwrap();
        }

        // Connect all remaining ports to output
        for (i, port) in last_ports.iter().enumerate() {
            let to_port = graph.input(output, i).unwrap();
            graph.link_ports(*port, to_port).unwrap();
        }

        GraphData { graph, weights }
    }
}

impl GraphGenerator for RandomGenerator {
    fn generate(&mut self, width: usize, depth: usize, num_graphs: usize) -> Vec<GraphData> {
        (0..num_graphs)
            .map(|_| self.generate_single(width, depth))
            .collect()
    }
}
