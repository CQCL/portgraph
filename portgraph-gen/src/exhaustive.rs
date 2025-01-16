use crate::generator::{GraphGenerator, GraphData};

pub struct ExhaustiveGenerator;

impl ExhaustiveGenerator {
    pub fn new() -> Self {
        Self
    }
}

impl GraphGenerator for ExhaustiveGenerator {
    fn generate(&mut self, width: usize, depth: usize, num_graphs: usize) -> Vec<GraphData> {
        // TODO: Implement exhaustive generation
        // For now, return empty vector
        Vec::new()
    }
}
