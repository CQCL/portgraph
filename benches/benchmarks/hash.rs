use std::{collections::HashMap, hash::DefaultHasher, time::Duration};

use criterion::{black_box, criterion_group, AxisScale, BenchmarkId, Criterion, PlotConfiguration};
use fxhash::FxHasher;
use portgraph::{
    hash::{AcyclicHash, GraphHash, WeisfeilerLehmanSparseHash, WeissfeilerLehmanHash},
    NodeIndex, PortGraph, SecondaryMap, UnmanagedDenseMap, Weights,
};
use serde::Deserialize;

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

fn bench_hash<H: GraphHash<Operation, ()> + Default>(c: &mut Criterion) {
    let mut g = c.benchmark_group("hashing init");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));
    g.warm_up_time(Duration::from_millis(500));
    g.measurement_time(Duration::from_secs(1));

    for size in [100, 1_000, 10_000] {
        let name = format!("{} hashing", std::any::type_name::<H>());
        g.bench_with_input(BenchmarkId::new(name, size), &size, |b, size| {
            let folder_path = format!("bench_data/{}", size);

            let n_files = std::fs::read_dir(&folder_path)
                .unwrap()
                .filter(|entry| entry.as_ref().unwrap().path().extension() == Some("json".as_ref()))
                .count();
            let mut graph_data = Vec::with_capacity(n_files);
            for i in 0..n_files {
                let file_path = format!("{}/graph_{}.json", folder_path, i);
                let file = std::fs::File::open(file_path).unwrap();
                let reader = std::io::BufReader::new(file);
                let data: GraphData = serde_json::from_reader(reader).unwrap();
                graph_data.push((data.graph, to_weights(data.weights)));
            }

            let mut iter = 0;
            let hasher = H::default();
            b.iter_batched(
                || {
                    let data = &graph_data[iter % n_files];
                    iter += 1;
                    data
                },
                |data| black_box(hasher.hash(&data.0, &data.1)),
                criterion::BatchSize::LargeInput,
            )
        });
    }
    g.finish();
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

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets =
        // bench_hash<AcyclicHash<FxHasher>>,
        bench_hash<WeissfeilerLehmanHash<FxHasher>>,
        bench_hash<WeisfeilerLehmanSparseHash<FxHasher>>,
}
