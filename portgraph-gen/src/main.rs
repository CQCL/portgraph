use clap::Parser;
use serde::Serialize;
use std::path::PathBuf;

mod exhaustive;
mod generator;
mod random;

use generator::GraphGenerator;

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

    /// Generation method (random or exhaustive)
    #[arg(long, default_value = "random")]
    method: String,
}

#[derive(Clone, Copy, Debug, Serialize)]
pub enum Operation {
    Input,
    Output,
    Op1,
    Op2,
    Op3,
}

impl Operation {
    fn random(rng: &mut impl rand::Rng) -> Self {
        match rng.gen_range(0..3) {
            0 => Operation::Op1,
            1 => Operation::Op2,
            _ => Operation::Op3,
        }
    }
}

fn main() {
    let args = Args::parse();

    // Create generator based on method
    let mut generator: Box<dyn GraphGenerator> = match args.method.as_str() {
        "random" => Box::new(random::RandomGenerator::new(42)),
        "exhaustive" => Box::new(exhaustive::ExhaustiveGenerator::new()),
        _ => panic!("Unknown generation method: {}", args.method),
    };

    // Generate graphs
    let graphs = generator.generate(args.width, args.depth, args.num_circuits);

    // Create output directory if it doesn't exist
    std::fs::create_dir_all(&args.output_dir).unwrap();

    // Save graphs
    for (i, graph_data) in graphs.into_iter().enumerate() {
        let file = args.output_dir.join(format!("graph_{}.json", i));
        let file = std::fs::File::create(file).unwrap();
        serde_json::to_writer_pretty(file, &graph_data).unwrap();
    }
}
