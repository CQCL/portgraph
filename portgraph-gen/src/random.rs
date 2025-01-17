use crate::{
    builder::GraphBuilder,
    generator::{GraphData, GraphGenerator},
    Operation,
};
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
        let mut builder = GraphBuilder::new(width);

        // Generate operations and add them to the builder
        for _ in 0..depth {
            let (op, i, j) = self.generate_operation(width);
            builder.add_operation(op, i, j);
        }

        builder.finish()
    }
}

impl GraphGenerator for RandomGenerator {
    fn generate(&mut self, width: usize, depth: usize, num_graphs: usize) -> Vec<GraphData> {
        (0..num_graphs)
            .map(|_| self.generate_single(width, depth))
            .collect()
    }
}
