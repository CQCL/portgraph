use clap::Parser;
use portgraph::{LinkMut, NodeIndex, PortGraph, PortIndex, PortMut, PortView};
use rand::prelude::*;
use serde::Serialize;
use std::{collections::HashMap, path::PathBuf};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Width of the graph (number of parallel operations)
    #[arg(short, long)]
    width: usize,

    /// Depth of the graph (number of operations between input and output)
    #[arg(short, long)]
    depth: usize,

    /// Number of circuits to generate
    #[arg(short, long)]
    num_circuits: usize,

    /// Output directory
    #[arg(short, long, default_value = "./out/")]
    output_dir: PathBuf,
}

#[derive(Clone, Copy, Debug, Serialize)]
enum Operation {
    Input,
    Output,
    Op1,
    Op2,
    Op3,
}

impl Operation {
    fn random(rng: &mut impl Rng) -> Self {
        match rng.gen_range(0..3) {
            0 => Operation::Op1,
            1 => Operation::Op2,
            _ => Operation::Op3,
        }
    }
}

#[derive(Serialize)]
struct GraphData {
    graph: PortGraph,
    weights: HashMap<NodeIndex, Operation>,
}

fn generate_operation(width: usize, rng: &mut impl Rng) -> (Operation, usize, usize) {
    let i = rng.gen_range(0..width);
    let mut j = rng.gen_range(0..width);
    while j == i {
        j = rng.gen_range(0..width);
    }
    (Operation::random(rng), i, j)
}

fn generate_graph(width: usize, depth: usize, rng: &mut impl Rng) -> GraphData {
    let mut graph = PortGraph::new();
    let mut weights = HashMap::new();

    // Create input node with w output ports
    let input = graph.add_node(0, width);
    weights.insert(input, Operation::Input);

    // Create output node with w input ports
    let output = graph.add_node(width, 0);
    weights.insert(output, Operation::Output);

    // Generate operations and their indices
    let operations: Vec<(Operation, usize, usize)> =
        (0..depth).map(|_| generate_operation(width, rng)).collect();

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
    for (i, &port) in last_ports.iter().enumerate() {
        let to_port = graph.input(output, i).unwrap();
        graph.link_ports(port, to_port).unwrap();
    }

    GraphData { graph, weights }
}

fn main() {
    let args = Args::parse();

    // Create output directory if it doesn't exist
    std::fs::create_dir_all(&args.output_dir).expect("Failed to create output directory");

    let mut rng = rand::thread_rng();

    for i in 0..args.num_circuits {
        let graph_data = generate_graph(args.width, args.depth, &mut rng);

        // Save graph as JSON
        let output_path = args.output_dir.join(format!("graph_{}.json", i));
        std::fs::write(
            output_path,
            serde_json::to_string_pretty(&graph_data).expect("Failed to serialize graph"),
        )
        .expect("Failed to write graph to file");
    }
}
