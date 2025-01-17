use portgraph::PortOffset;
use std::{collections::BTreeSet, mem};

use crate::{
    builder::GraphBuilder,
    generator::{GraphData, GraphGenerator},
    Operation,
};

pub struct ExhaustiveGenerator;

type OperationLayer = Vec<(Operation, usize, usize)>;

impl ExhaustiveGenerator {
    pub fn new() -> Self {
        Self
    }

    fn generate_layers<'a>(
        &'a self,
        width: usize,
        max_ops: usize,
        last_indices: &'a BTreeSet<usize>,
    ) -> impl Iterator<Item = OperationLayer> + 'a {
        GenLayer {
            last_layer: Vec::new(),
            width,
            max_ops,
            last_indices,
        }
    }
}

struct GenLayer<'a> {
    last_layer: OperationLayer,
    width: usize,
    max_ops: usize,
    last_indices: &'a BTreeSet<usize>,
}

impl Iterator for GenLayer<'_> {
    type Item = OperationLayer;

    fn next(&mut self) -> Option<Self::Item> {
        let mut n_ops = self.last_layer.len();
        while let Some(last) = self.last_layer.pop() {
            let used_indices = all_used_indices(&self.last_layer);
            let next = next_op(&last, &used_indices, &self.last_indices, self.width);
            if let Some(next) = next {
                self.last_layer.push(next);
                break;
            }
        }

        if self.last_layer.is_empty() {
            n_ops += 1;
            if n_ops > self.max_ops {
                return None;
            }
        }

        while self.last_layer.len() < n_ops {
            let used_indices = all_used_indices(&self.last_layer);
            let start = self.last_layer.iter().map(|(_, i, _)| i).max();
            let start = start.map(|s| s + 1).unwrap_or(0);
            let fst_index = (start..self.width).find(|i| !used_indices.contains(i))?;
            // Incrementing this dummy op should give us the first valid op
            let dummy_op_zero = (Operation::Op3, fst_index, fst_index);
            let next = next_op(
                &dummy_op_zero,
                &used_indices,
                &self.last_indices,
                self.width,
            )?;
            self.last_layer.push(next);
        }

        Some(self.last_layer.clone())
    }
}

impl Operation {
    fn increment(&self) -> Option<Self> {
        match self {
            Operation::Op1 => Some(Operation::Op2),
            Operation::Op2 => Some(Operation::Op3),
            Operation::Op3 => None,
            _ => unreachable!(),
        }
    }
}

fn increment_index(
    mut index: usize,
    other_index: usize,
    used_indices: &BTreeSet<usize>,
    last_indices: &BTreeSet<usize>,
    max: usize,
) -> Option<usize> {
    while index + 1 < max {
        index += 1;
        if used_indices.contains(&index) {
            continue;
        }
        if !last_indices.contains(&other_index) && !last_indices.contains(&index) {
            continue;
        }
        return Some(index);
    }
    None
}

fn next_op(
    &(op, i, j): &(Operation, usize, usize),
    used_indices: &BTreeSet<usize>,
    last_indices: &BTreeSet<usize>,
    max_width: usize,
) -> Option<(Operation, usize, usize)> {
    if let Some(next_op) = op.increment() {
        return Some((next_op, i, j));
    }
    let next_op = Operation::Op1;

    let next_j = increment_index(j, i, &used_indices, last_indices, max_width);
    if let Some(next_j) = next_j {
        return Some((next_op, i, next_j));
    }

    let next_i = (i + 1..).find(|i| !used_indices.contains(i)).unwrap();
    let next_j = increment_index(next_i, next_i, &used_indices, last_indices, max_width);
    if let Some(next_j) = next_j {
        return Some((next_op, next_i, next_j));
    }

    None
}

fn all_used_indices(last_layer: &[(Operation, usize, usize)]) -> BTreeSet<usize> {
    last_layer.iter().flat_map(|&(_, i, j)| [i, j]).collect()
}

impl GraphGenerator for ExhaustiveGenerator {
    fn generate(&mut self, width: usize, depth: usize, num_graphs: usize) -> Vec<GraphData> {
        let mut results = Vec::with_capacity(num_graphs);

        let mut last_graphs = vec![(GraphBuilder::new(width), BTreeSet::from_iter(0..width))];
        while results.len() < num_graphs {
            let mut new_last_graphs = Vec::new();
            for (graph, last_indices) in mem::take(&mut last_graphs) {
                let max_ops = depth - graph.n_operations();
                for layer in self.generate_layers(width, max_ops, &last_indices) {
                    let mut graph_clone = graph.clone();
                    let mut last_indices = BTreeSet::new();
                    for (op, i, j) in layer {
                        graph_clone.add_operation(op, i, j);
                        last_indices.extend([i, j]);
                    }
                    results.push(graph_clone.clone().finish());
                    new_last_graphs.push((graph_clone, last_indices));
                }
            }
            if new_last_graphs.is_empty() {
                break;
            }
            last_graphs = mem::take(&mut new_last_graphs);
        }

        results.shrink_to_fit();
        results
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use insta::assert_debug_snapshot;
    use portgraph::{
        algorithms::{toposort, TopoSort},
        Direction, LinkView, PortView,
    };

    #[test]
    fn test_generate_layers() {
        let generator = ExhaustiveGenerator::new();
        let last_indices = BTreeSet::from([0, 1, 2, 3]);
        let layers: Vec<_> = generator.generate_layers(4, 2, &last_indices).collect();
        assert_debug_snapshot!(layers);
    }

    #[test]
    fn test_generate_layers_2() {
        let generator = ExhaustiveGenerator::new();
        let last_indices = BTreeSet::from([0]);
        let layers: Vec<_> = generator.generate_layers(3, 1, &last_indices).collect();
        assert_debug_snapshot!(layers);
    }

    #[test]
    fn test_generate_layers_empty() {
        let generator = ExhaustiveGenerator::new();
        let last_indices = BTreeSet::new();
        let layers: Vec<_> = generator.generate_layers(2, 1, &last_indices).collect();
        assert!(layers.is_empty());
    }

    #[test]
    fn test_small_exhaustive_generation() {
        let mut generator = ExhaustiveGenerator::new();
        let graphs = generator.generate(2, 2, 10);
        let all_ops: Vec<_> = graphs.iter().map(|g| as_operations_vec(g)).collect();
        assert_debug_snapshot!(all_ops);
    }

    fn as_operations_vec(data: &GraphData) -> Vec<(Operation, usize, usize)> {
        let input_node = data
            .graph
            .nodes_iter()
            .find(|n| data.weights[n] == Operation::Input)
            .unwrap();
        let output_node = data
            .graph
            .nodes_iter()
            .find(|n| data.weights[n] == Operation::Output)
            .unwrap();
        let num_paths = data.graph.outputs(input_node).count();
        let mut port_to_qubit = BTreeMap::new();

        for path_index in 0..num_paths {
            let mut current_node = input_node;
            let mut current_offset = path_index;

            while current_node != output_node {
                let current_port = data.graph.output(current_node, current_offset).unwrap();
                let next_port = data.graph.port_link(current_port).unwrap();
                let next_node = data.graph.port_node(next_port).unwrap();
                port_to_qubit.insert(current_port, path_index);
                port_to_qubit.insert(next_port, path_index);

                current_node = next_node;
                current_offset = data.graph.port_offset(next_port).unwrap().index();
            }
        }

        let topo: TopoSort<_> = toposort(&data.graph, [input_node], Direction::Outgoing);
        topo.into_iter()
            .filter(|n| !matches!(data.weights[n], Operation::Input | Operation::Output))
            .map(|n| {
                (
                    data.weights[&n],
                    port_to_qubit[&data.graph.input(n, 0).unwrap()],
                    port_to_qubit[&data.graph.input(n, 1).unwrap()],
                )
            })
            .collect()
    }
}
