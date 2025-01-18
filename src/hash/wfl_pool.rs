use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use itertools::Itertools;
use petgraph::unionfind::UnionFind;

use crate::{LinkView, NodeIndex, PortGraph, PortView, SecondaryMap, UnmanagedDenseMap, Weights};

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

fn node_is_sink<H: Hasher + Default>(
    node: NodeIndex,
    graph: &mut UfGraph<H>,
    hashes: &BTreeMap<NodeIndex, u64>,
) -> bool {
    smallest_neighbour(node, graph, hashes) == node
}

struct UfGraph<H> {
    nodes: UnionFind<usize>,
    edges: UnmanagedDenseMap<NodeIndex, BTreeMap<NodeIndex, u64>>,
    _hasher: PhantomData<H>,
}

impl<H> UfGraph<H> {
    fn from_portgraph(graph: &PortGraph, hashes: &BTreeMap<NodeIndex, u64>) -> Self
    where
        H: Hasher + Default,
    {
        let nodes = UnionFind::new(graph.node_capacity());
        let mut ret = Self {
            nodes,
            edges: Default::default(),
            _hasher: PhantomData,
        };

        for n in graph.nodes_iter() {
            for (this_port, other_port) in graph.output_links(n) {
                let other_node = graph.port_node(other_port).unwrap();

                let this_hash = hashes[&n];
                let other_hash = hashes[&other_node];

                let mut hasher = H::default();
                (this_hash, this_port, other_port, other_hash).hash(&mut hasher);
                let edge_hash = hasher.finish();

                let mut opp_hasher = H::default();
                (other_hash, other_port, this_port, this_hash).hash(&mut opp_hasher);
                let opp_edge_hash = opp_hasher.finish();

                ret.add_edge(n, other_node, edge_hash, opp_edge_hash);
            }
        }

        ret
    }

    fn add_edge(&mut self, src: NodeIndex, tgt: NodeIndex, edge_hash: u64, opp_edge_hash: u64)
    where
        H: Hasher + Default,
    {
        let src = self.root_node(src);
        let tgt = self.root_node(tgt);
        assert_ne!(src, tgt);

        let [src_edges, tgt_edges] = self.edges.get_disjoint_mut([src, tgt]).unwrap();
        add_or_hash_edge::<H>(src_edges, tgt, edge_hash);
        add_or_hash_edge::<H>(tgt_edges, src, opp_edge_hash);
    }

    fn root_node(&self, node: NodeIndex) -> NodeIndex {
        NodeIndex::new(self.nodes.find(node.index()))
    }

    fn neighbours(&self, node: NodeIndex) -> &BTreeMap<NodeIndex, u64>
    where
        H: Hasher + Default,
    {
        let node = self.root_node(node);
        self.edges.get(node)
    }

    /// Contract two nodes and merge all edges.
    fn contract(&mut self, node1: NodeIndex, node2: NodeIndex)
    where
        H: Hasher + Default,
    {
        let node1 = self.root_node(node1);
        let node2 = self.root_node(node2);
        if !self.nodes.union(node1.index(), node2.index()) {
            return;
        }

        let new_root = self.root_node(node1);
        assert!([node1, node2].contains(&new_root));
        let non_root = if new_root == node1 { node2 } else { node1 };

        // Move over all edges of the now non-root node
        let non_root_edges = self.edges.take(non_root);
        for (tgt, edge_hash) in non_root_edges {
            if tgt != new_root {
                let [new_root_edges, tgt_edges] =
                    self.edges.get_disjoint_mut([new_root, tgt]).unwrap();
                add_or_hash_edge::<H>(new_root_edges, tgt, edge_hash);
                let opp_edge_hash = tgt_edges.remove(&non_root).unwrap();
                add_or_hash_edge::<H>(tgt_edges, new_root, opp_edge_hash);
            } else {
                let new_root_edges = self.edges.get_mut(new_root);
                new_root_edges.remove(&non_root);
            }
        }
    }
}

fn add_or_hash_edge<H: Hasher + Default>(
    edges: &mut BTreeMap<NodeIndex, u64>,
    tgt: NodeIndex,
    edge_hash: u64,
) {
    if let Some(curr_edge_hash) = edges.get_mut(&tgt) {
        let mut hasher = H::default();
        curr_edge_hash.hash(&mut hasher);
        edge_hash.hash(&mut hasher);
        *curr_edge_hash = hasher.finish();
    } else {
        edges.insert(tgt, edge_hash);
    }
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

        let mut roots = graph.nodes_iter().collect_vec();
        // Initialise UF data structure
        let mut uf_graph = UfGraph::<H>::from_portgraph(graph, &hashes);

        // Reset at every iteration. Hoisted out for reuse
        let mut visited = BTreeSet::new();
        loop {
            if roots.len() <= 1 {
                break;
            }
            let n_roots_bef = roots.len();
            roots.retain(|&n| node_is_sink(n, &mut uf_graph, &hashes));
            let n_roots_aft = roots.len();
            if n_roots_aft == n_roots_bef {
                // No more progress will be made
                break;
            }

            let partitions = roots
                .iter_mut()
                .map(|root| {
                    let partition = find_partition(*root, &mut uf_graph, &hashes);
                    (root, partition)
                })
                .collect_vec();

            for (root, partition) in partitions {
                visited.clear();
                // Contract partition and update the root
                *root = dfs_contract_partition(
                    *root,
                    &mut uf_graph,
                    &partition,
                    &mut hashes,
                    &mut visited,
                )
                .unwrap();
            }
        }

        roots
            .into_iter()
            .fold(0, |acc, n| acc ^ *hashes.get(&n).unwrap())
    }

    fn name(&self) -> String {
        format!("Pool-WFL({} hops)", self.n_hops)
    }
}

/// Return the new root of the contracted graph
fn dfs_contract_partition<H: Hasher + Default>(
    node: NodeIndex,
    uf_graph: &mut UfGraph<H>,
    partition_nodes: &BTreeSet<NodeIndex>,
    hashes: &mut BTreeMap<NodeIndex, u64>,
    visited: &mut BTreeSet<NodeIndex>,
) -> Option<NodeIndex> {
    if !partition_nodes.contains(&node) {
        // Do not contract nodes that are not part of the partition
        return None;
    }
    if !visited.insert(node) {
        // Can contract, but do not proceed recursively, already visited
        return Some(node);
    }
    let mut hasher = H::default();
    let neighs = uf_graph.neighbours(node).to_owned();
    for (neigh, edge_hash) in neighs {
        if let Some(neigh) =
            dfs_contract_partition::<H>(neigh, uf_graph, partition_nodes, hashes, visited)
        {
            hashes[&neigh].hash(&mut hasher);
            edge_hash.hash(&mut hasher);
            uf_graph.contract(node, neigh);
        }
    }
    hashes[&node].hash(&mut hasher);
    let node = uf_graph.root_node(node);
    hashes.insert(node, hasher.finish());
    Some(node)
}

fn find_partition<H: Hasher + Default>(
    node: NodeIndex,
    uf_graph: &UfGraph<H>,
    hashes: &BTreeMap<NodeIndex, u64>,
) -> BTreeSet<NodeIndex> {
    let mut nodes = BTreeSet::from_iter([node]);
    let mut node_queue = VecDeque::with_capacity(uf_graph.neighbours(node).len());
    node_queue.push_back(node);
    while let Some(node) = node_queue.pop_front() {
        for &neigh in uf_graph.neighbours(node).keys() {
            if smallest_neighbour(neigh, uf_graph, hashes) != node {
                continue;
            }
            if !nodes.insert(neigh) {
                continue;
            }
            node_queue.push_back(neigh);
        }
    }
    nodes
}

fn smallest_neighbour<H: Hasher + Default>(
    node: NodeIndex,
    graph: &UfGraph<H>,
    hashes: &BTreeMap<NodeIndex, u64>,
) -> NodeIndex {
    let neighs = [node]
        .into_iter()
        .chain(graph.neighbours(node).into_iter().map(|(&n, _)| n));
    neighs.min_by_key(|&n| hashes[&n]).unwrap_or(node)
}
