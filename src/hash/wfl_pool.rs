use std::{
    collections::{BTreeMap, BTreeSet},
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem,
};

use itertools::Itertools;

use crate::{LinkView, NodeIndex, PortGraph, PortView, Weights};

use super::wfl::wfl_hash;

/// Hasher for graphs using the Weisfeiler-Lehman algorithm.
#[derive(Debug, Clone)]
pub struct PoolWFLHash<H> {
    n_hops: usize,
    _hasher: PhantomData<H>,
}

impl<H> Default for PoolWFLHash<H> {
    fn default() -> Self {
        Self {
            n_hops: 1,
            _hasher: Default::default(),
        }
    }
}

impl<H> PoolWFLHash<H> {
    /// Create a new hasher.
    pub fn new(n_hops: usize) -> Self {
        Self {
            n_hops,
            _hasher: PhantomData,
        }
    }
}

fn node_is_sink(
    node: NodeIndex,
    get_neighbours: &FindNeighbours<impl Hasher + Default>,
    hashes: &BTreeMap<NodeIndex, u64>,
) -> bool {
    let mut all_neigh_vals = get_neighbours
        .neighbours(node)
        .into_iter()
        .map(|(n, _)| hashes.get(&n));
    let self_val = hashes.get(&node);
    all_neigh_vals.all(|v| v >= self_val)
}

impl<H: Hasher + Default + Clone, N: Clone + Hash, P: Clone + Hash> super::GraphHash<N, P>
    for PoolWFLHash<H>
{
    /// Hash a graph using the Weisfeiler-Lehman algorithm.
    fn hash<'a>(&'a self, graph: &'a PortGraph, weights: &'a Weights<N, P>) -> u64 {
        let mut hashes = BTreeMap::new();

        // Initialise hashes with a round of WFL
        let mut cache = BTreeMap::new();
        for n in graph.nodes_iter() {
            hashes.insert(
                n,
                wfl_hash::<H, _, _>(n, graph, weights, self.n_hops, &mut cache),
            );
        }

        // Pool recursively
        let mut sinks = graph.nodes_iter().collect_vec();
        // For each sink, the neighbouring sinks
        let mut boundaries = None;

        loop {
            if sinks.len() <= 1 {
                break;
            }
            let n_sinks_bef = sinks.len();
            let find_neighbours = &FindNeighbours::<H>::new(graph, &boundaries, &hashes);
            sinks.retain(|&n| node_is_sink(n, find_neighbours, &hashes));
            let n_sinks_aft = sinks.len();
            if n_sinks_aft == n_sinks_bef {
                // No more progress will be made
                break;
            }

            let mut new_boundaries = Vec::new();
            let mut new_hashes = BTreeMap::new();

            let mut node_to_sink = BTreeMap::new();

            for &sink in &sinks {
                let mut new_boundary = Vec::new();
                let mut sink_hasher = H::default();

                let (nodes_here, nodes_beyond) = update_hash::<H>(
                    sink,
                    find_neighbours,
                    &mut sink_hasher,
                    H::default(),
                    &hashes,
                    &mut Default::default(),
                );
                let sink_hash = sink_hasher.finish();
                new_hashes.insert(sink, sink_hash);

                node_to_sink.extend(nodes_here.into_iter().map(|n| (n, sink)));
                new_boundary.extend(nodes_beyond);
                new_boundaries.push((sink, new_boundary));
            }

            boundaries = Some(apply_sink_map(new_boundaries, &node_to_sink));
            hashes = mem::take(&mut new_hashes);
        }

        sinks
            .into_iter()
            .fold(0, |acc, n| acc ^ *hashes.get(&n).unwrap())
    }

    fn name(&self) -> String {
        format!("Pool-WFL({} hops)", self.n_hops)
    }
}

fn apply_sink_map(
    new_boundaries: Vec<(NodeIndex, Vec<(NodeIndex, u64)>)>,
    node_to_sink: &BTreeMap<NodeIndex, NodeIndex>,
) -> BTreeMap<NodeIndex, Vec<(NodeIndex, u64)>> {
    new_boundaries
        .into_iter()
        .map(|(sink, nodes)| {
            let nodes = nodes
                .into_iter()
                .map(|(n, u)| (node_to_sink[&n], u))
                .collect();
            (sink, nodes)
        })
        .collect()
}

enum FindNeighbours<'a, H> {
    PortGraph {
        hashes: &'a BTreeMap<NodeIndex, u64>,
        graph: &'a PortGraph,
        _hasher: PhantomData<H>,
    },
    BoundaryMap {
        boundaries: &'a BTreeMap<NodeIndex, Vec<(NodeIndex, u64)>>,
    },
}

impl<'a, H: Hasher + Default> FindNeighbours<'a, H> {
    fn new(
        graph: &'a PortGraph,
        boundaries: &'a Option<BTreeMap<NodeIndex, Vec<(NodeIndex, u64)>>>,
        hashes: &'a BTreeMap<NodeIndex, u64>,
    ) -> Self {
        if let Some(boundaries) = boundaries {
            Self::BoundaryMap { boundaries }
        } else {
            Self::PortGraph {
                graph,
                hashes,
                _hasher: PhantomData,
            }
        }
    }

    fn neighbours(&self, node: NodeIndex) -> Vec<(NodeIndex, u64)> {
        match self {
            FindNeighbours::PortGraph { graph, hashes, .. } => graph
                .all_links(node)
                .map(|(this_port, other_port)| {
                    let other_node = graph.port_node(other_port).unwrap();
                    let mut hasher = H::default();
                    let edge_data = (
                        hashes.get(&node).unwrap(),
                        graph.port_offset(this_port).unwrap(),
                        graph.port_offset(other_port).unwrap(),
                        hashes.get(&other_node).unwrap(),
                    );
                    edge_data.hash(&mut hasher);
                    (other_node, hasher.finish())
                })
                .collect(),
            FindNeighbours::BoundaryMap { boundaries } => boundaries.get(&node).unwrap().clone(),
        }
    }
}

fn update_hash<H: Hasher + Default>(
    node: NodeIndex,
    get_neighbours: &FindNeighbours<impl Hasher + Default>,
    sink_hasher: &mut impl Hasher,
    path_hasher: impl Hasher + Clone,
    hashes: &BTreeMap<NodeIndex, u64>,
    visited: &mut BTreeSet<NodeIndex>,
) -> (Vec<NodeIndex>, Vec<(NodeIndex, u64)>) {
    if !visited.insert(node) {
        return (Vec::new(), Vec::new());
    }

    // Record our visit
    sink_hasher.write_u64(path_hasher.finish());
    sink_hasher.write_u64(hashes[&node]);

    // Go to neighbours
    let mut nodes_here = vec![node];
    let mut nodes_beyond = Vec::new();
    for (n, u) in get_neighbours.neighbours(node) {
        if smallest_neighbour(n, get_neighbours, hashes) == node {
            // Visit neighbours as they are in the same sink partition
            let mut path_hasher = path_hasher.clone();
            path_hasher.write_u64(u);
            let (new_here, new_beyond) = update_hash::<H>(
                n,
                &get_neighbours,
                sink_hasher,
                path_hasher,
                hashes,
                visited,
            );
            nodes_here.extend(new_here);
            nodes_beyond.extend(new_beyond);
        } else {
            // Do not visit neighbour, mark as beyond our lands
            nodes_beyond.push((n, u));
        }
    }
    (nodes_here, nodes_beyond)
}

fn smallest_neighbour(
    node: NodeIndex,
    get_neighbours: &FindNeighbours<impl Hasher + Default>,
    hashes: &BTreeMap<NodeIndex, u64>,
) -> NodeIndex {
    let neighs = [node]
        .into_iter()
        .chain(get_neighbours.neighbours(node).into_iter().map(|(n, _)| n));
    neighs.min_by_key(|&n| hashes[&n]).unwrap_or(node)
}
