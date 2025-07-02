//! This module provides functionality for convexity checking in directed acyclic graphs.
use crate::algorithms::{toposort, ConvexChecker};
use crate::{
    Direction, LinkError, LinkMut, LinkView, NodeIndex, PortIndex, PortMut, PortOffset, PortView,
};
use delegate::delegate;
use std::cmp::{max, min};
use std::collections::{HashMap, HashSet, VecDeque};
use thiserror::Error;

/// Error type for [`DynamicTopoSort`].
#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum DynamicTopoSortError {
    /// The referenced node has not been added to the topological order.
    #[error("{node:?} has not been added to the topological order.")]
    InvalidNode {
        /// The missing node.
        node: NodeIndex,
    },
    /// Connecting the nodes would create a cycle.
    #[error("Connecting {from:?} to {to:?} would create a cycle in the DAG.")]
    WouldCreateCycle {
        /// Source of the edge.
        from: NodeIndex,
        /// Target of the edge.
        to: NodeIndex,
    },
}
/// Maintains a dynamic topological order for a directed acyclic graph (DAG) using Pearce and Kelly's algorithm.
#[derive(Default, Clone, Debug)]
pub struct DynamicTopoSort {
    // Current topological order
    order: Vec<NodeIndex>,
    // Node ID to position in `order`
    node_to_pos: HashMap<NodeIndex, usize>,
}

impl DynamicTopoSort {
    /// Initializes the topological order for the given graph.
    pub fn with_graph<G: LinkView + PortView>(graph: &G) -> Self {
        let num_nodes_hint = graph.nodes_iter().size_hint().1.unwrap_or_default();
        let mut topo = Self {
            order: Vec::with_capacity(num_nodes_hint),
            node_to_pos: HashMap::new(),
        };
        let source = graph
            .nodes_iter()
            .filter(|&n| graph.input_neighbours(n).next().is_none());
        let topo_order = toposort::<_, HashSet<PortIndex>>(graph, source, Direction::Outgoing);
        topo.order = topo_order.collect();
        for (i, &node) in topo.order.iter().enumerate() {
            topo.node_to_pos.insert(node, i);
        }
        topo
    }

    /// Adds a new node to the graph, placing it at the end of the order.
    pub fn add_node(&mut self, node: NodeIndex) {
        if self.node_to_pos.contains_key(&node) {
            return; // Node already exists
        }
        let pos = self.order.len();
        self.order.push(node);
        self.node_to_pos.insert(node, pos);
    }

    /// Adds an edge and updates the topological order, returning an error if a cycle is created.
    pub fn connect_nodes<G: LinkView>(
        &mut self,
        from: NodeIndex,
        to: NodeIndex,
        graph: &G,
    ) -> Result<(), DynamicTopoSortError> {
        if !self.node_to_pos.contains_key(&from) {
            return Err(DynamicTopoSortError::InvalidNode { node: from });
        }
        if !self.node_to_pos.contains_key(&to) {
            return Err(DynamicTopoSortError::InvalidNode { node: to });
        }
        if self.would_create_cycle(from, to, graph) {
            return Err(DynamicTopoSortError::WouldCreateCycle { from, to });
        }
        let from_pos = *self.node_to_pos.get(&from).unwrap();
        let to_pos = *self.node_to_pos.get(&to).unwrap();
        if from_pos >= to_pos {
            self.update_order(from, to, graph);
        }
        Ok(())
    }

    /// Removes a node and updates the topological order.
    pub fn remove_node(&mut self, node: NodeIndex) -> Result<(), DynamicTopoSortError> {
        if let Some(pos) = self.node_to_pos.remove(&node) {
            self.order.remove(pos);
            for (i, &n) in self.order.iter().enumerate() {
                self.node_to_pos.insert(n, i);
            }
            Ok(())
        } else {
            Err(DynamicTopoSortError::InvalidNode { node })
        }
    }

    /// Removes an edge and updates the topological order if necessary.
    pub fn disconnect_nodes<G: LinkView>(
        &mut self,
        from: NodeIndex,
        to: NodeIndex,
        _graph: &G,
    ) -> Result<(), DynamicTopoSortError> {
        if !self.node_to_pos.contains_key(&from) {
            return Err(DynamicTopoSortError::InvalidNode { node: from });
        }
        if !self.node_to_pos.contains_key(&to) {
            return Err(DynamicTopoSortError::InvalidNode { node: to });
        }
        Ok(())
    }

    /// Checks if `start` can reach `target` via existing edges (standard BFS for cycle detection).
    fn would_create_cycle<G: LinkView>(&self, from: NodeIndex, to: NodeIndex, graph: &G) -> bool {
        let from_pos = *self.node_to_pos.get(&from).unwrap_or(&usize::MAX);
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(to); // Start from 'to'
        while let Some(node) = queue.pop_front() {
            if node == from {
                // If 'from' is reachable from 'to', a cycle exists
                return true;
            }
            if visited.insert(node) {
                for neighbor in graph.output_neighbours(node) {
                    let neighbor_pos = *self.node_to_pos.get(&neighbor).unwrap_or(&usize::MAX);
                    if neighbor_pos <= from_pos {
                        // Only check nodes before 'from' in order
                        queue.push_back(neighbor);
                    }
                }
            }
        }
        false
    }

    /// Updates the topological order after adding an edge (from, to).
    fn update_order<G: LinkView>(&mut self, from: NodeIndex, to: NodeIndex, graph: &G) {
        let from_pos = *self.node_to_pos.get(&from).unwrap();
        let to_pos = *self.node_to_pos.get(&to).unwrap();
        if from_pos < to_pos {
            return;
        }
        let lb = to_pos;
        let ub = from_pos;
        let delta_f = self.cone(to, ub, graph, Direction::Outgoing);
        let delta_b = self.cone(from, lb, graph, Direction::Incoming);
        let mut new_pos = to_pos;
        for w in delta_b.into_iter().chain(delta_f) {
            self.order[new_pos] = w;
            self.node_to_pos.insert(w, new_pos);
            new_pos += 1;
        }
    }

    /// Computes the future cone from a starting node, up to position `ub`.
    fn cone<G: LinkView>(
        &self,
        start: NodeIndex,
        bound: usize,
        graph: &G,
        dir: Direction,
    ) -> Vec<NodeIndex> {
        let mut visited = HashSet::new();
        let mut cone = Vec::new();
        self.dfs(start, &mut visited, &mut cone, bound, graph, dir);
        cone
    }

    fn dfs<G: LinkView>(
        &self,
        n: NodeIndex,
        visited: &mut HashSet<NodeIndex>,
        cone: &mut Vec<NodeIndex>,
        bound: usize,
        graph: &G,
        dir: Direction,
    ) -> bool {
        let pos = *self.node_to_pos.get(&n).unwrap();
        let out_of_bounds = match dir {
            Direction::Outgoing => pos >= bound,
            Direction::Incoming => pos <= bound,
        };
        if visited.contains(&n) || out_of_bounds {
            return false;
        }
        visited.insert(n);
        cone.push(n);
        if dir == Direction::Outgoing {
            for neighbor in graph.output_neighbours(n) {
                if self.dfs(neighbor, visited, cone, bound, graph, dir) {
                    return true;
                }
            }
        } else {
            for neighbor in graph.input_neighbours(n) {
                if self.dfs(neighbor, visited, cone, bound, graph, dir) {
                    return true;
                }
            }
        }
        false
    }

    /// Returns the current topological order (for testing or inspection).
    #[allow(dead_code)]
    pub fn get_order(&self) -> &Vec<NodeIndex> {
        &self.order
    }

    fn has_path_outside_subgraph<G: LinkView>(
        &self,
        start: NodeIndex,
        end: NodeIndex,
        min_pos: usize,
        max_pos: usize,
        nodes: &HashSet<NodeIndex>,
        graph: &G,
    ) -> bool {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(start);
        while let Some(node) = queue.pop_front() {
            if !nodes.contains(&node) && node != start {
                return true;
            }
            if node == end {
                continue;
            }
            if visited.insert(node) {
                for n in graph.output_neighbours(node) {
                    let n_pos = *self.node_to_pos.get(&n).unwrap_or(&usize::MAX);
                    if n_pos >= min_pos && n_pos <= max_pos {
                        queue.push_back(n);
                    }
                }
            }
        }
        false
    }

    /// Checks if `start` can reach any input within position bounds, going outside `nodes`.
    fn can_reach_inputs<G: LinkView + PortView>(
        &self,
        start: NodeIndex,
        min_pos: usize,
        max_pos: usize,
        nodes: &HashSet<NodeIndex>,
        inputs: &[PortIndex],
        graph: &G,
    ) -> bool {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back((start, false));
        while let Some((node, has_exited)) = queue.pop_front() {
            if visited.contains(&node) {
                continue;
            }
            visited.insert(node);
            let pos = *self.node_to_pos.get(&node).unwrap_or(&usize::MAX);
            if pos < min_pos || pos > max_pos {
                continue;
            }
            let is_outside = !nodes.contains(&node) && node != start;
            let current_exited = has_exited || is_outside;
            if current_exited {
                for &input in inputs {
                    if graph.port_node(input) == Some(node) {
                        return true; // Reached an input via a path that exited the subgraph
                    }
                }
            }
            for n in graph.input_neighbours(node) {
                let n_pos = *self.node_to_pos.get(&n).unwrap_or(&usize::MAX);
                if n_pos >= min_pos && n_pos <= max_pos {
                    queue.push_back((n, current_exited));
                }
            }
        }
        false
    }
}

/// A dynamic topological convex checker for portgraphs.
pub struct DynamicTopoConvexChecker<G> {
    topo_sort: DynamicTopoSort,
    graph: G,
}

impl<G> DynamicTopoConvexChecker<G>
where
    G: LinkView + PortView,
{
    /// Creates a new convexity checker for the given graph.
    pub fn new(graph: G) -> Self {
        Self {
            topo_sort: DynamicTopoSort::with_graph(&graph),
            graph,
        }
    }
}

/// Implement PortView for DynamicTopoConvexChecker
impl<G: PortView> PortView for DynamicTopoConvexChecker<G> {
    delegate! {
        to self.graph {
            fn port_direction(&self, port: impl Into<PortIndex>) -> Option<Direction>;
            fn port_node(&self, port: impl Into<PortIndex>) -> Option<NodeIndex>;
            fn port_offset(&self, port: impl Into<PortIndex>) -> Option<PortOffset>;
            fn port_index(&self, node: NodeIndex, offset: PortOffset) -> Option<PortIndex>;
            fn ports(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = PortIndex> + Clone;
            fn all_ports(&self, node: NodeIndex) -> impl Iterator<Item = PortIndex> + Clone;
            fn input(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn output(&self, node: NodeIndex, offset: usize) -> Option<PortIndex>;
            fn num_ports(&self, node: NodeIndex, direction: Direction) -> usize;
            fn port_offsets(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = PortOffset> + Clone;
            fn all_port_offsets(&self, node: NodeIndex) -> impl Iterator<Item = PortOffset> + Clone;
            fn contains_node(&self, node: NodeIndex) -> bool;
            fn contains_port(&self, port: PortIndex) -> bool;
            fn is_empty(&self) -> bool;
            fn node_count(&self) -> usize;
            fn port_count(&self) -> usize;
            fn nodes_iter(&self) -> impl Iterator<Item = NodeIndex> + Clone;
            fn ports_iter(&self) -> impl Iterator<Item = PortIndex> + Clone;
            fn node_capacity(&self) -> usize;
            fn port_capacity(&self) -> usize;
            fn node_port_capacity(&self, node: NodeIndex) -> usize;
        }
    }
}

/// Implement LinkView for DynamicTopoConvexChecker
impl<G: LinkView> LinkView for DynamicTopoConvexChecker<G> {
    type LinkEndpoint = G::LinkEndpoint;

    delegate! {
        to self.graph {
            fn get_connections(&self, from: NodeIndex, to: NodeIndex) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone;
            fn port_links(&self, port: PortIndex) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone;
            fn links(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone;
            fn all_links(&self, node: NodeIndex) -> impl Iterator<Item = (Self::LinkEndpoint, Self::LinkEndpoint)> + Clone;
            fn neighbours(&self, node: NodeIndex, direction: Direction) -> impl Iterator<Item = NodeIndex> + Clone;
            fn all_neighbours(&self, node: NodeIndex) -> impl Iterator<Item = NodeIndex> + Clone;
            fn link_count(&self) -> usize;
        }
    }
}

/// Implement PortMut for DynamicTopoConvexChecker
impl<G: PortMut> PortMut for DynamicTopoConvexChecker<G> {
    fn add_node(&mut self, inputs: usize, outputs: usize) -> NodeIndex {
        let node = self.graph.add_node(inputs, outputs);
        self.topo_sort.add_node(node);
        node
    }

    fn remove_node(&mut self, node: NodeIndex) {
        self.graph.remove_node(node);
        self.topo_sort.remove_node(node).expect("Node not found");
    }

    delegate! {
        to self.graph {
            fn clear(&mut self);
            fn reserve(&mut self, nodes: usize, ports: usize);
            fn set_num_ports<F: FnMut(PortIndex, crate::portgraph::PortOperation)>(&mut self, node: NodeIndex, inputs: usize, outputs: usize, rekey: F);
            fn swap_nodes(&mut self, a: NodeIndex, b: NodeIndex);
            fn compact_nodes<F: FnMut(NodeIndex, NodeIndex)>(&mut self, rekey: F);
            fn compact_ports<F: FnMut(PortIndex, PortIndex)>(&mut self, rekey: F);
            fn shrink_to_fit(&mut self);
        }
    }
}

/// Implement LinkMut for DynamicTopoConvexChecker
impl<G: LinkMut> LinkMut for DynamicTopoConvexChecker<G> {
    fn link_ports(
        &mut self,
        from: PortIndex,
        to: PortIndex,
    ) -> Result<(G::LinkEndpoint, G::LinkEndpoint), LinkError> {
        let from_node = self
            .graph
            .port_node(from)
            .ok_or(LinkError::UnknownPort { port: from })?;
        let to_node = self
            .graph
            .port_node(to)
            .ok_or(LinkError::UnknownPort { port: to })?;
        if self
            .topo_sort
            .would_create_cycle(to_node, from_node, &self.graph)
        {
            panic!("Adding this edge would create a cycle");
        }
        let result = self.graph.link_ports(from, to)?;
        self.topo_sort
            .connect_nodes(from_node, to_node, &self.graph)
            .map_err(|e| match e {
                DynamicTopoSortError::InvalidNode { .. } => LinkError::UnknownPort { port: from },
                DynamicTopoSortError::WouldCreateCycle { .. } => {
                    panic!("Cycle detected despite earlier check")
                }
            })?;
        Ok(result)
    }

    fn unlink_port(&mut self, port: PortIndex) -> Option<G::LinkEndpoint> {
        let result = self.graph.unlink_port(port);
        if result.is_some() {
            // Note: We don’t have access to the linked port’s endpoint here, so we assume the disconnect logic is sufficient
            let from_node = self.graph.port_node(port).unwrap();
            // Simplification: Disconnect all outgoing edges from this node (could be refined)
            for to_node in self
                .graph
                .neighbours(from_node, Direction::Outgoing)
                .collect::<Vec<_>>()
            {
                self.topo_sort
                    .disconnect_nodes(from_node, to_node, &self.graph)
                    .expect("Edge not found");
            }
        }
        result
    }
}
impl<G> ConvexChecker for DynamicTopoConvexChecker<G>
where
    G: PortView + LinkView,
{
    fn is_convex(
        &self,
        nodes: impl IntoIterator<Item = NodeIndex>,
        inputs: impl IntoIterator<Item = PortIndex>,
        outputs: impl IntoIterator<Item = PortIndex>,
    ) -> bool {
        let nodes: HashSet<NodeIndex> = nodes.into_iter().collect();
        for &node in &nodes {
            if !self.topo_sort.node_to_pos.contains_key(&node) {
                return false;
            }
        }
        if nodes.len() < 2 {
            return true;
        }
        let inputs: Vec<PortIndex> = inputs.into_iter().collect();
        let outputs: Vec<PortIndex> = outputs.into_iter().collect();
        let mut min_pos = usize::MAX;
        let mut max_pos = 0;

        for &node in &nodes {
            if let Some(&pos) = self.topo_sort.node_to_pos.get(&node) {
                min_pos = min(min_pos, pos);
                max_pos = max(max_pos, pos);
            } else {
                return false;
            }
        }

        if inputs.is_empty() && outputs.is_empty() {
            for &start in &nodes {
                for &end in &nodes {
                    if start == end {
                        continue;
                    }
                    let start_pos = *self.topo_sort.node_to_pos.get(&start).unwrap();
                    let end_pos = *self.topo_sort.node_to_pos.get(&end).unwrap();
                    if start_pos < end_pos
                        && self.topo_sort.has_path_outside_subgraph(
                            start,
                            end,
                            min_pos,
                            max_pos,
                            &nodes,
                            &self.graph,
                        )
                    {
                        return false;
                    }
                }
            }
            return true;
        }

        for &output in &outputs {
            if let Some(output_node) = self.graph.port_node(output) {
                if !nodes.contains(&output_node) {
                    continue;
                }
                if self.topo_sort.can_reach_inputs(
                    output_node,
                    min_pos,
                    max_pos,
                    &nodes,
                    &inputs,
                    &self.graph,
                ) {
                    return false;
                }
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::ConvexChecker;
    use crate::{LinkMut, NodeIndex, PortGraph};
    use std::collections::HashSet;

    #[test]
    fn test_convex_with_ports() {
        // Create a graph: n0 -> n1 -> n2
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1); // Input node: 0 in, 1 out
        let n1 = graph.add_node(1, 1); // Middle node: 1 in, 1 out
        let n2 = graph.add_node(1, 0); // Output node: 1 in, 0 out
        graph.link_nodes(n0, 0, n1, 0).unwrap(); // n0 output 0 to n1 input 0
        graph.link_nodes(n1, 0, n2, 0).unwrap(); // n1 output 0 to n2 input 0

        // Create the checker
        let checker = DynamicTopoConvexChecker::new(graph);

        // Subgraph with just n1, using n1's own ports
        let nodes = HashSet::from([n1]);
        let inputs = vec![checker.graph.input(n1, 0).unwrap()]; // n1's input port
        let outputs = vec![checker.graph.output(n1, 0).unwrap()]; // n1's output port
        assert!(
            checker.is_convex(nodes.clone(), inputs, outputs),
            "Subgraph {{n1}} should be convex as paths stay within it"
        );

        // Non-convex case: subgraph {n0, n2}
        let nodes_non_convex = HashSet::from([n0, n2]);
        let inputs = vec![checker.graph.output(n0, 0).unwrap()]; // n0's output port
        let outputs = vec![checker.graph.input(n2, 0).unwrap()]; // n2's input port
        assert!(
            !checker.is_convex(nodes_non_convex, inputs, outputs),
            "Path goes through n1, which is outside {{n0, n2}}, so it’s not convex"
        );
    }

    fn is_valid_topological_order<G: LinkView>(topo: &DynamicTopoSort, graph: &G) -> bool {
        for &node in topo.get_order() {
            let node_pos = *topo.node_to_pos.get(&node).unwrap();
            for neighbor in graph.output_neighbours(node) {
                let neighbor_pos = *topo.node_to_pos.get(&neighbor).unwrap();
                if node_pos >= neighbor_pos {
                    return false;
                }
            }
        }
        true
    }

    #[test]
    fn test_basic_linear_order() {
        // Create a PortGraph and add nodes with ports
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1); // Node with 1 output port
        let n1 = graph.add_node(1, 1); // Node with 1 input and 1 output port
        let n2 = graph.add_node(1, 0); // Node with 1 input port

        // Connect nodes: n0 -> n1 -> n2
        graph.link_nodes(n0, 0, n1, 0).unwrap();
        graph.link_nodes(n1, 0, n2, 0).unwrap();

        // Initialize DynamicTopoSort with the graph
        let topo = DynamicTopoSort::with_graph(&graph);

        // Verify the topological order
        assert_eq!(topo.get_order(), &vec![n0, n1, n2]);
        assert!(is_valid_topological_order(&topo, &graph));
    }

    #[test]
    fn test_reordering() {
        // Create a PortGraph with nodes n0, n1, n2
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(1, 0); // n0 has 1 input (from n1)
        let n1 = graph.add_node(0, 1); // n1 has 1 output (to n0)
        let n2 = graph.add_node(0, 0); // n2 has no ports

        // Initialize DynamicTopoSort with the graph (no edges yet)
        let mut topo = DynamicTopoSort::with_graph(&graph);
        assert_eq!(topo.get_order(), &vec![n0, n1, n2]); // Initial order

        // Add edge n1 -> n0 and update topological order
        topo.connect_nodes(n1, n0, &graph).unwrap();
        graph.link_nodes(n1, 0, n0, 0).unwrap(); // Add the edge to the graph

        // Check the updated order
        assert_eq!(topo.get_order(), &vec![n1, n0, n2]);
        assert!(is_valid_topological_order(&topo, &graph));
    }

    #[test]
    fn test_indirect_cycle() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1); // n0: 1 output
        let n1 = graph.add_node(1, 1); // n1: 1 input, 1 output
        let n2 = graph.add_node(1, 1); // n2: 1 input, 1 output
        let n3 = graph.add_node(1, 0); // n3: 1 input
        graph.link_nodes(n0, 0, n1, 0).unwrap();
        graph.link_nodes(n1, 0, n2, 0).unwrap();
        graph.link_nodes(n2, 0, n3, 0).unwrap();

        let mut topo = DynamicTopoSort::with_graph(&graph);
        match topo.connect_nodes(n3, n0, &graph) {
            Ok(()) => panic!("Should have detected cycle"),
            Err(e) => assert_eq!(
                e,
                DynamicTopoSortError::WouldCreateCycle { from: n3, to: n0 }
            ),
        }
        assert_eq!(topo.get_order(), &vec![n0, n1, n2, n3]);
        assert!(is_valid_topological_order(&topo, &graph));
    }

    #[test]
    fn test_multiple_paths() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 2); // 0 inputs, 2 outputs
        let n1 = graph.add_node(1, 1); // 1 input, 1 output
        let n2 = graph.add_node(1, 1); // 1 input, 1 output
        let n3 = graph.add_node(2, 0); // 2 inputs, 0 outputs

        graph.link_nodes(n0, 0, n1, 0).unwrap(); // n0 -> n1
        graph.link_nodes(n0, 1, n2, 0).unwrap(); // n0 -> n2
        graph.link_nodes(n1, 0, n3, 0).unwrap(); // n1 -> n3
        graph.link_nodes(n2, 0, n3, 1).unwrap(); // n2 -> n3

        let topo = DynamicTopoSort::with_graph(&graph);
        let order = topo.get_order();
        assert_eq!(order[0], n0);
        assert!(order[1] == n1 || order[1] == n2);
        assert!(order[2] == if order[1] == n1 { n2 } else { n1 });
        assert_eq!(order[3], n3);
        assert!(is_valid_topological_order(&topo, &graph));
    }

    #[test]
    fn test_add_existing_node() {
        // Create a new PortGraph and add a node
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 0); // Node with 0 inputs and 0 outputs

        // Initialize DynamicTopoSort with the graph
        let mut topo = DynamicTopoSort::with_graph(&graph);
        assert_eq!(topo.get_order(), &vec![n0]); // Initial order should be [n0]

        // Attempt to add the same node again
        topo.add_node(n0); // Should do nothing since n0 is already in node_to_pos
        assert_eq!(topo.get_order(), &vec![n0]); // Order should remain [n0]

        // Verify the topological order is valid
        assert!(is_valid_topological_order(&topo, &graph));
    }

    #[test]
    fn test_connect_nodes_nonexistent_node() {
        let graph = PortGraph::new();
        let mut topo = DynamicTopoSort::with_graph(&graph);
        let n0 = Node::node_from_usize(0);
        let n1 = Node::node_from_usize(1);
        match topo.connect_nodes(n0, n1, &graph) {
            Ok(()) => panic!("Should have failed"),
            Err(e) => assert_eq!(e, DynamicTopoSortError::InvalidNode { node: n0 }),
        }
    }

    #[test]
    fn test_no_edges() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 0);
        let n1 = graph.add_node(0, 0);
        let n2 = graph.add_node(0, 0);
        let topo = DynamicTopoSort::with_graph(&graph);
        let order = topo.get_order();
        let nodes: HashSet<_> = order.iter().cloned().collect();
        assert_eq!(nodes.len(), 3);
        assert!(nodes.contains(&n0));
        assert!(nodes.contains(&n1));
        assert!(nodes.contains(&n2));
        assert!(is_valid_topological_order(&topo, &graph));
    }

    #[test]
    fn test_disconnected_graph() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1); // 0 in, 1 out
        let n1 = graph.add_node(1, 0); // 1 in, 0 out
        let n2 = graph.add_node(0, 1); // 0 in, 1 out
        let n3 = graph.add_node(1, 0); // 1 in, 0 out
        graph.link_nodes(n0, 0, n1, 0).unwrap(); // n0 -> n1
        graph.link_nodes(n2, 0, n3, 0).unwrap(); // n2 -> n3
        let topo = DynamicTopoSort::with_graph(&graph);
        let order = topo.get_order();
        let pos_n0 = order.iter().position(|&x| x == n0).unwrap();
        let pos_n1 = order.iter().position(|&x| x == n1).unwrap();
        let pos_n2 = order.iter().position(|&x| x == n2).unwrap();
        let pos_n3 = order.iter().position(|&x| x == n3).unwrap();
        assert!(pos_n0 < pos_n1);
        assert!(pos_n2 < pos_n3);
        assert!(is_valid_topological_order(&topo, &graph));
    }

    #[test]
    fn test_connecting_components() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(1, 1); // 0 in, 1 out
        let n1 = graph.add_node(1, 0); // 1 in, 0 out
        let n2 = graph.add_node(0, 1); // 0 in, 1 out
        let mut topo = DynamicTopoSort::with_graph(&graph);

        // Connect n0 -> n1
        topo.connect_nodes(n0, n1, &graph).unwrap();
        graph.link_nodes(n0, 0, n1, 0).unwrap();

        // Connect n2 -> n0
        topo.connect_nodes(n2, n0, &graph).unwrap();
        graph.link_nodes(n2, 0, n0, 0).unwrap();

        let order = topo.get_order();
        let pos_n2 = order.iter().position(|&x| x == n2).unwrap();
        let pos_n0 = order.iter().position(|&x| x == n0).unwrap();
        let pos_n1 = order.iter().position(|&x| x == n1).unwrap();
        assert!(pos_n2 < pos_n0, "n2 should precede n0");
        assert!(pos_n0 < pos_n1, "n0 should precede n1");
        assert!(is_valid_topological_order(&topo, &graph));
    }

    #[test]
    fn test_reorder_middle() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1);
        let n1 = graph.add_node(1, 1);
        let n2 = graph.add_node(1, 1);
        let n3 = graph.add_node(1, 0);
        let mut topo = DynamicTopoSort::with_graph(&graph);

        topo.connect_nodes(n0, n2, &graph).unwrap();
        graph.link_nodes(n0, 0, n2, 0).unwrap();
        topo.connect_nodes(n1, n3, &graph).unwrap();
        graph.link_nodes(n1, 0, n3, 0).unwrap();
        topo.connect_nodes(n2, n1, &graph).unwrap();
        graph.link_nodes(n2, 0, n1, 0).unwrap();

        assert_eq!(topo.get_order(), &vec![n0, n2, n1, n3]);
        assert!(is_valid_topological_order(&topo, &graph));
    }

    #[test]
    fn test_remove_node() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1);
        let n1 = graph.add_node(1, 1);
        let n2 = graph.add_node(1, 0);
        graph.link_nodes(n0, 0, n1, 0).unwrap();
        graph.link_nodes(n1, 0, n2, 0).unwrap();
        let mut topo = DynamicTopoSort::with_graph(&graph);

        topo.remove_node(n1).unwrap();
        graph.remove_node(n1);

        assert_eq!(topo.get_order(), &vec![n0, n2]);
        assert!(!topo.node_to_pos.contains_key(&n1));
        assert!(is_valid_topological_order(&topo, &graph));

        let n3 = Node::node_from_usize(3);
        match topo.remove_node(n3) {
            Err(e) => assert_eq!(e, DynamicTopoSortError::InvalidNode { node: n3 }),
            _ => panic!("Should have failed"),
        }
    }

    #[test]
    fn test_disconnect_nodes() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1);
        let n1 = graph.add_node(1, 1);
        let n2 = graph.add_node(1, 0);
        graph.link_nodes(n0, 0, n1, 0).unwrap();
        graph.link_nodes(n1, 0, n2, 0).unwrap();
        let mut topo = DynamicTopoSort::with_graph(&graph);

        topo.disconnect_nodes(n0, n1, &graph).unwrap();
        let out_port_n0 = graph.output(n0, 0).unwrap();
        graph.unlink_port(out_port_n0);

        assert!(graph.output_neighbours(n0).next().is_none());
        assert_eq!(graph.output_neighbours(n1).collect::<Vec<_>>(), vec![n2]);
        assert!(is_valid_topological_order(&topo, &graph));

        topo.disconnect_nodes(n0, n2, &graph).unwrap();
    }

    #[test]
    fn test_remove_isolated_node() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 0);
        let n1 = graph.add_node(0, 0);
        let n2 = graph.add_node(0, 0);
        let mut topo = DynamicTopoSort::with_graph(&graph);

        topo.remove_node(n1).unwrap();
        graph.remove_node(n1);

        assert_eq!(topo.get_order(), &vec![n0, n2]);
        assert!(!topo.node_to_pos.contains_key(&n1));
        assert!(is_valid_topological_order(&topo, &graph));
    }

    #[test]
    fn test_remove_node_in_chain() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1); // 0 in, 1 out
        let n1 = graph.add_node(1, 1); // 1 in, 1 out
        let n2 = graph.add_node(1, 0); // 1 in, 0 out
        graph.link_nodes(n0, 0, n1, 0).unwrap(); // n0 -> n1
        graph.link_nodes(n1, 0, n2, 0).unwrap(); // n1 -> n2

        let mut checker = DynamicTopoConvexChecker::new(graph.clone());
        checker.topo_sort.remove_node(n1).unwrap();
        graph.remove_node(n1);

        assert_eq!(checker.topo_sort.get_order(), &vec![n0, n2]);
        assert!(!checker.topo_sort.node_to_pos.contains_key(&n1));
        assert!(is_valid_topological_order(&checker.topo_sort, &graph));
    }

    #[test]
    fn test_remove_node_with_multiple_edges() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1);
        let n1 = graph.add_node(1, 2); // 1 in, 2 out
        let n2 = graph.add_node(1, 1);
        let n3 = graph.add_node(1, 0);
        graph.link_nodes(n0, 0, n1, 0).unwrap(); // n0 -> n1
        graph.link_nodes(n1, 0, n2, 0).unwrap(); // n1 -> n2
        graph.link_nodes(n2, 0, n3, 0).unwrap(); // n2 -> n3

        let mut checker = DynamicTopoConvexChecker::new(graph.clone());
        checker.topo_sort.remove_node(n1).unwrap();
        graph.remove_node(n1);

        assert_eq!(checker.topo_sort.get_order(), &vec![n0, n2, n3]);
        assert!(!checker.topo_sort.node_to_pos.contains_key(&n1));
        assert!(is_valid_topological_order(&checker.topo_sort, &graph));
    }

    #[test]
    fn test_disconnect_edge_in_complex_graph() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 2); // 0 in, 2 out
        let n1 = graph.add_node(1, 1); // 1 in, 1 out
        let n2 = graph.add_node(2, 0); // 2 in, 0 out
        graph.link_nodes(n0, 0, n1, 0).unwrap(); // n0 -> n1
        graph.link_nodes(n0, 1, n2, 0).unwrap(); // n0 -> n2
        graph.link_nodes(n1, 0, n2, 1).unwrap(); // n1 -> n2

        let mut checker = DynamicTopoConvexChecker::new(graph.clone());
        checker.topo_sort.disconnect_nodes(n0, n1, &graph).unwrap();

        let out_port_n0 = graph.output(n0, 0).unwrap();
        graph.unlink_port(out_port_n0);

        assert_eq!(graph.output_neighbours(n0).collect::<Vec<_>>(), vec![n2]);
        assert_eq!(graph.output_neighbours(n1).collect::<Vec<_>>(), vec![n2]);
        assert_eq!(checker.topo_sort.get_order(), &vec![n0, n1, n2]);
        assert!(is_valid_topological_order(&checker.topo_sort, &graph));
    }

    #[test]
    fn test_sequence_of_operations() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 1);
        let n1 = graph.add_node(1, 1);
        let n2 = graph.add_node(1, 0);
        graph.link_nodes(n0, 0, n1, 0).unwrap();
        graph.link_nodes(n1, 0, n2, 0).unwrap();

        let mut checker = DynamicTopoConvexChecker::new(graph.clone());
        checker.topo_sort.remove_node(n1).unwrap();
        graph.remove_node(n1);

        assert_eq!(checker.topo_sort.get_order(), &vec![n0, n2]);

        let n3 = graph.add_node(1, 0);
        checker.topo_sort.add_node(n3);
        graph.link_nodes(n0, 0, n3, 0).unwrap();
        checker.topo_sort.connect_nodes(n0, n3, &graph).unwrap();

        assert_eq!(checker.topo_sort.get_order(), &vec![n0, n2, n3]);
        assert!(is_valid_topological_order(&checker.topo_sort, &graph));
    }

    #[test]
    fn test_operations_on_empty_graph() {
        let graph = PortGraph::new();
        let mut checker = DynamicTopoConvexChecker::new(graph.clone());
        let n0 = Node::node_from_usize(0);
        let n1 = Node::node_from_usize(1);

        match checker.topo_sort.remove_node(n0) {
            Err(e) => assert_eq!(e, DynamicTopoSortError::InvalidNode { node: n0 }),
            _ => panic!("Should have failed"),
        }

        match checker.topo_sort.disconnect_nodes(n0, n1, &graph) {
            Err(e) => assert_eq!(e, DynamicTopoSortError::InvalidNode { node: n0 }),
            _ => panic!("Should have failed"),
        }
    }

    #[test]
    fn test_convex_subgraph() {
        let mut graph = PortGraph::new();
        let n0 = graph.add_node(0, 2); // 0 in, 2 out
        let n1 = graph.add_node(1, 1); // 1 in, 1 out
        let n2 = graph.add_node(1, 1); // 1 in, 1 out
        let n3 = graph.add_node(2, 0); // 2 in, 0 out
        graph.link_nodes(n0, 0, n1, 0).unwrap();
        graph.link_nodes(n0, 1, n2, 0).unwrap();
        graph.link_nodes(n1, 0, n3, 0).unwrap();
        graph.link_nodes(n2, 0, n3, 1).unwrap();

        let checker = DynamicTopoConvexChecker::new(graph);
        let subgraph = HashSet::from([n0, n3]);
        assert!(
            !checker.is_convex(subgraph, vec![], vec![]),
            "Subgraph {{0, 3}} should not be convex"
        );

        let subgraph2 = HashSet::from([n1, n2, n3]);
        assert!(
            checker.is_convex(subgraph2, vec![], vec![]),
            "Subgraph {{1, 2, 3}} should be convex"
        );

        let subgraph3 = HashSet::from([n0, n1, n3]);
        assert!(
            !checker.is_convex(subgraph3, vec![], vec![]),
            "Subgraph {{0, 1, 3}} should not be convex"
        );
    }

    #[test]
    fn test_empty_or_invalid_subgraph() {
        let graph = PortGraph::new();
        let checker = DynamicTopoConvexChecker::new(graph);
        let empty_subgraph: HashSet<NodeIndex> = HashSet::new();
        assert!(
            checker.is_convex(empty_subgraph, vec![], vec![]),
            "Empty subgraph should be convex"
        );

        let mut graph = PortGraph::new();
        let _n0 = graph.add_node(0, 0);
        let checker = DynamicTopoConvexChecker::new(graph);
        let invalid_subgraph = HashSet::from([Node::node_from_usize(1)]);
        assert!(
            !checker.is_convex(invalid_subgraph, vec![], vec![]),
            "Subgraph with invalid node should not be convex"
        );
    }
}
