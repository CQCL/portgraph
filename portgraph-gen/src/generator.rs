use crate::Operation;
use portgraph::NodeIndex;
use portgraph::PortGraph;
use serde::Serialize;
use std::collections::HashMap;

#[derive(Debug, Serialize)]
pub struct GraphData {
    pub graph: PortGraph,
    pub weights: HashMap<NodeIndex, Operation>,
}

pub trait GraphGenerator {
    fn generate(&mut self, width: usize, depth: usize, num_graphs: usize) -> Vec<GraphData>;
}
