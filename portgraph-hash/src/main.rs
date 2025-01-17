use anyhow::{Context, Result};
use clap::Parser;
use fxhash::FxHasher;
use portgraph::hash::{
    AcyclicHash, GraphHash, HistWFLHash, WeisfeilerLehmanHash, WeisfeilerLehmanSparseHash,
};
use portgraph::{NodeIndex, PortGraph, SecondaryMap, UnmanagedDenseMap, Weights};
use serde::Deserialize;
use std::cmp;
use std::collections::{BTreeSet, HashMap};
use std::path::PathBuf;

#[derive(Clone, Copy, Debug, Deserialize, Default, Hash)]
enum Operation {
    #[default]
    Input,
    Output,
    Op1,
    Op2,
    Op3,
}

#[derive(Deserialize)]
struct GraphData {
    graph: PortGraph,
    weights: HashMap<NodeIndex, Operation>,
}

#[derive(Parser)]
#[command(author, version, about)]
struct Args {
    /// Directory containing graph files
    #[arg(value_name = "DIR")]
    graph_dir: PathBuf,

    /// Only process the first n graphs
    #[arg(short = 'n', long = "num-graphs")]
    num_graphs: Option<usize>,
}

fn main() -> Result<()> {
    let hashers = [
        Box::new(AcyclicHash::<FxHasher>::new()) as Box<dyn GraphHash<Operation, ()>>,
        Box::new(WeisfeilerLehmanHash::<FxHasher>::new(1)),
        Box::new(WeisfeilerLehmanHash::<FxHasher>::new(2)),
        Box::new(HistWFLHash::<FxHasher>::new(1)),
        Box::new(HistWFLHash::<FxHasher>::new(2)),
        Box::new(WeisfeilerLehmanSparseHash::<FxHasher>::new(1)),
        Box::new(WeisfeilerLehmanSparseHash::<FxHasher>::new(2)),
        Box::new(WeisfeilerLehmanSparseHash::<FxHasher>::new(3)),
        Box::new(WeisfeilerLehmanSparseHash::<FxHasher>::new(4)),
    ];

    let args = Args::parse();

    // Gather and sort all valid graph file paths
    let mut graph_files: Vec<_> = std::fs::read_dir(&args.graph_dir)
        .with_context(|| format!("Failed to read directory {}", args.graph_dir.display()))?
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            if path.is_file() && path.extension().map_or(false, |ext| ext == "json") {
                Some(path)
            } else {
                None
            }
        })
        .collect();
    graph_files.sort();

    let n_graphs = cmp::min(
        graph_files.len(),
        args.num_graphs.unwrap_or(graph_files.len()),
    );

    println!(
        "Found {} graph files, processing {}",
        graph_files.len(),
        n_graphs
    );

    graph_files.truncate(n_graphs);

    // Store hashes for each hasher
    let mut hash_sets: Vec<BTreeSet<u64>> = vec![BTreeSet::new(); hashers.len()];
    let mut collision_counts: Vec<usize> = vec![0; hashers.len()];
    let mut duplicate_counts = 0;

    // Read all graph files and compute their hashes
    for path in graph_files {
        let content = std::fs::read_to_string(&path)
            .with_context(|| format!("Failed to read file {}", path.display()))?;
        let data: GraphData = serde_json::from_str(&content)
            .with_context(|| format!("Failed to parse JSON from {}", path.display()))?;

        let graph = &data.graph;
        let weights = to_weights(data.weights);

        // Compute hashes using all hashers
        let hashes: Vec<u64> = hashers
            .iter()
            .map(|hasher| hasher.hash(&graph, &weights))
            .collect();

        let inserted: Vec<bool> = hashes
            .iter()
            .enumerate()
            .map(|(i, &hash)| hash_sets[i].insert(hash))
            .collect();
        let all_inserted = inserted.iter().all(|&x| x);
        let none_inserted = inserted.iter().all(|&x| !x);

        if all_inserted {
            println!("File {}: OK", path.display());
        } else if none_inserted {
            duplicate_counts += 1;
            println!("File {}: DUPLICATE", path.display());
        } else {
            // panic!("We do not tolerate collisions");
            for (i, &inserted) in inserted.iter().enumerate() {
                if !inserted {
                    println!(
                        "COLLISION FOUND for file {} (hasher {:?})",
                        path.display(),
                        hashers[i].name()
                    );
                    collision_counts[i] += 1;
                }
            }
        }
    }

    let n_distinct_graphs = n_graphs - duplicate_counts;

    // Print collision counts for each hasher
    for (hasher, &collisions) in hashers.iter().zip(collision_counts.iter()) {
        println!(
            "Collision rate for hasher {:?}: {:.2}%",
            hasher.name(),
            100. * (collisions as f64) / (n_distinct_graphs as f64)
        );
    }

    Ok(())
}

fn to_weights(weights: HashMap<NodeIndex, Operation>) -> Weights<Operation, ()> {
    let mut map = UnmanagedDenseMap::<NodeIndex, Operation>::new();
    for (key, value) in weights {
        map.set(key, value);
    }
    Weights {
        nodes: map,
        ports: SecondaryMap::new(),
    }
}
