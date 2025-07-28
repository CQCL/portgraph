use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use itertools::Itertools;
use smallvec::SmallVec;

use crate::algorithms::{toposort, TopoSort};
use crate::{Direction, LinkView, NodeIndex, PortIndex, SecondaryMap, UnmanagedDenseMap};

use super::ConvexChecker;

/// The number of lines that we preallocate space for on the stack.
///
/// This is the maximum expected number of lines for any subgraph we are checking
/// the convexity of.
const MAX_LINES: usize = 8;

/// The number of lines that we preallocate space for on the stack for each node.
///
/// This is the maximum expected number of lines that any node in the graph
/// will belong to.
const MAX_LINES_ON_NODE: usize = 4;

/// Convexity checking using a pre-computed line partition of the graph.
///
/// The main concept is that of a line interval, see [`LineInterval`] and
/// [`LineIntervals`]. The idea is that once a graph has been partitioned into
/// edge-disjoint paths (called lines), then a convex subgraph corresponds to
/// a set of intervals on each of the lines.
///
/// Note that not every subgraph that can be expressed as line intervals is
/// convex, so further checks are required once intervals are found.
#[derive(Debug, Clone, PartialEq)]
pub struct LineConvexChecker<G> {
    graph: G,
    /// Map from nodes to the lines they belong to and their position on them.
    node_to_pos: UnmanagedDenseMap<NodeIndex, LinePositions>,
    /// List of all lines, as sequence of the nodes on them.
    ///
    /// Note that the node positions on one line are not guaranteed to be
    /// contiguous, however they will always be strictly increasing according
    /// to the direction of the edges on the lines.
    lines: Vec<Vec<NodeIndex>>,
    /// Memory allocated once and reused in the `get_intervals` method.
    #[allow(clippy::type_complexity)]
    get_intervals_scratch_space: RefCell<SmallVec<[(Option<LineIndex>, Vec<Position>); MAX_LINES]>>,
}

/// Position of a node on all lines it belongs to.
///
/// The position is the same on all lines, hence a single integer is enough.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
struct LinePositions {
    /// The index of the lines in the partition.
    line_indices: SmallVec<[LineIndex; MAX_LINES_ON_NODE]>,
    /// The position of the node on the lines.
    ///
    /// The node is at the same position on every line, hence a single integer
    /// is enough.
    position: Position,
}

/// Index of a line in a [`LineConvexChecker`]' s line partition.
// u32 is enough as the number of lines is always smaller than the total
// number of nodes.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LineIndex(pub u32);
impl LineIndex {
    fn as_usize(self) -> usize {
        self.0 as usize
    }
}

/// Position of a node on a line in a [`LineConvexChecker`]' s line partition.
// u32 is enough as it is always smaller than the total number of nodes.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Position(pub u32);
impl Position {
    fn next(self) -> Self {
        Self(self.0 + 1)
    }
}

/// Intervals of positions on each line that are occupied by a subgraph.
///
/// This is a map from line indices to intervals. It is optimised for small
/// numbers of lines.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LineIntervals(SmallVec<[(LineIndex, LineInterval); MAX_LINES]>);

impl LineIntervals {
    /// Get the interval for the given line.
    pub fn get(&self, line: LineIndex) -> Option<LineInterval> {
        let (_, interval) = self.iter().find(|&(l, _)| l == line)?;
        Some(interval)
    }

    fn get_mut(&mut self, line: LineIndex) -> Option<&mut LineInterval> {
        let (_, interval) = self.0.iter_mut().find(|(l, _)| *l == line)?;
        Some(interval)
    }

    /// Iterate over the intervals.
    ///
    /// The order in which the line indices are returned is unspecified.
    pub fn iter(&self) -> impl Iterator<Item = (LineIndex, LineInterval)> + '_ {
        self.0.iter().copied()
    }

    /// Iterate over the intervals, in no particular order.
    pub fn values(&self) -> impl Iterator<Item = LineInterval> + '_ {
        self.iter().map(|(_, interval)| interval)
    }
}

/// Interval of positions on a line, [min, max] inclusive.
///
/// We are not using Ranges as the intervals do not correspond to contiguous
/// range of integers (but a subsequence of it).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LineInterval {
    /// The minimum position on the line.
    pub min: Position,
    /// The maximum position on the line.
    pub max: Position,
}

impl<G> LineConvexChecker<G>
where
    G: LinkView + Clone,
{
    /// Create a new [`LineConvexChecker`].
    ///
    /// Will traverse all nodes in the graph in topological order, and thus runs
    /// in linear time in the size of the graph
    pub fn new(graph: G) -> Self {
        let inputs = graph
            .nodes_iter()
            .filter(|&n| graph.input_neighbours(n).count() == 0);
        let topsort: TopoSort<_> = toposort(graph.clone(), inputs, Direction::Outgoing);

        let mut extend_frontier = extend_line_ends_frontier(&graph);
        let mut node_to_pos =
            UnmanagedDenseMap::<_, LinePositions>::with_capacity(graph.node_count());
        let mut lines = Vec::new();

        // Compute the lines and position of each node and store them in the map.
        for node in topsort {
            let new_pos = extend_frontier(node);
            for &line_index in &new_pos.line_indices {
                if lines.len() <= line_index.as_usize() {
                    lines.extend(vec![vec![]; line_index.as_usize() - lines.len() + 1]);
                }
                lines[line_index.as_usize()].push(node);
            }
            node_to_pos.set(node, new_pos);
        }

        drop(extend_frontier); // borrow checker wants explicit drop

        Self {
            graph,
            node_to_pos,
            lines,
            get_intervals_scratch_space: RefCell::new(SmallVec::new()),
        }
    }

    /// Whether the subgraph induced by the node set is convex.
    ///
    /// An induced subgraph is convex if there is no node that is both in the
    /// past and in the future of some nodes in the subgraph.
    ///
    /// ## Arguments
    ///
    /// - `nodes`: The nodes inducing a subgraph of `self.graph()`.
    ///
    /// ## Algorithm
    ///
    /// First of all, we check that the nodes form contiguous intervals on
    /// the set of lines that they belong to. Checking for non-contiguous sets
    /// of nodes is a cheap way to detect many cases of non-convexity. If this
    /// passes, we then traverse the set of nodes in the future of the subgraph
    /// with a position smaller than the position of the nodes at the beginning
    /// of the line intervals of the subgraph. If none of these are on the same
    /// line as the inputs of the subgraph, the subgraph is convex.
    #[inline(always)]
    pub fn is_node_convex(&self, nodes: impl IntoIterator<Item = NodeIndex>) -> bool {
        let Some(intervals) = self.get_intervals(nodes) else {
            return false;
        };

        self.is_convex_by_intervals(intervals)
    }

    /// Check whether the subgraph given by `intervals` is convex.
    ///
    /// In other words, check if there is a path in `self.graph()` from an end
    /// of one interval to the start of another.
    pub fn is_convex_by_intervals(&self, intervals: LineIntervals) -> bool {
        let max_start_pos = intervals
            .values()
            .map(|LineInterval { min, .. }| min)
            .max()
            .unwrap();
        let mut future_nodes = VecDeque::from_iter(intervals.iter().filter_map(
            |(line, LineInterval { max, .. })| {
                let ind = self.find_index(line, max).expect("max not on line");
                self.lines[line.as_usize()].get(ind + 1).copied()
            },
        ));
        let mut visited = BTreeSet::new();

        // We must prove that all nodes in `future_nodes` are not in the past
        // of any node at the beginning of a line interval.
        while let Some(node) = future_nodes.pop_front() {
            if self.get_position(node) > max_start_pos {
                // we cannot be in the past of any node at the beginning of a
                // line interval, so we can stop searching
                continue;
            }
            if !visited.insert(node) {
                continue; // been here before
            }
            for &line in self.get_lines(node) {
                if let Some(LineInterval { min, max, .. }) = intervals.get(line) {
                    let pos = self.get_position(node);
                    debug_assert!(
                        pos < min || pos > max,
                        "node cannot be in interval [min, max]"
                    );
                    if pos < min {
                        // we are in the past of min, so there is a path from
                        // an output to an input! -> not convex
                        return false;
                    }
                }
            }

            future_nodes.extend(self.graph.output_neighbours(node));
        }

        true
    }

    /// Extend the given intervals to include the given node.
    ///
    /// Return whether the interval was successfully extended to contain `node`,
    /// i.e. whether adding `node` to the subgraph represented by the intervals
    /// results in another subgraph that can be expressed as line intervals.
    ///
    /// If `false` is returned, the `intervals` are left unchanged.
    #[must_use]
    pub fn try_extend_intervals(&self, intervals: &mut LineIntervals, node: NodeIndex) -> bool {
        // Backup the old intervals.
        let old_intervals = intervals.clone();

        let pos = self.get_position(node);
        let lines = self.get_lines(node);

        for &line in lines {
            if let Some(interval) = intervals.get_mut(line) {
                if pos < interval.min {
                    if self.line_positions_from(pos, line).nth(1) != Some(interval.min) {
                        *intervals = old_intervals;
                        return false;
                    }
                    interval.min = pos;
                } else if pos > interval.max {
                    if self.line_positions_from(interval.max, line).nth(1) != Some(pos) {
                        *intervals = old_intervals;
                        return false;
                    }
                    interval.max = pos;
                }
            } else {
                intervals
                    .0
                    .push((line, LineInterval { min: pos, max: pos }));
            }
        }

        true
    }

    /// Get the lines a node belongs to.
    #[inline(always)]
    pub fn get_lines(&self, node: NodeIndex) -> &[LineIndex] {
        &self.node_to_pos.get(node).line_indices
    }

    /// Get the position of a node on its lines.
    #[inline(always)]
    pub fn get_position(&self, node: NodeIndex) -> Position {
        self.node_to_pos.get(node).position
    }

    /// Get the intervals of positions on each line that are occupied by the nodes.
    ///
    /// Return `None` if the nodes do not form contiguous intervals on lines
    pub fn get_intervals(
        &self,
        nodes: impl IntoIterator<Item = NodeIndex>,
    ) -> Option<LineIntervals> {
        let nodes = nodes.into_iter();
        // An estimate of the number of nodes, used to pre-allocate Vecs.
        let num_nodes = nodes.size_hint().0;

        // A map from line index to the positions of the nodes on that line.
        // The map is stored as a SmallVec given that the number of lines is
        // typically less than 8.
        let mut line_to_pos = self.get_intervals_scratch_space.borrow_mut();
        small_map_clear(&mut line_to_pos);

        for node in nodes {
            let pos = self.get_position(node);
            for &l in self.get_lines(node) {
                small_map_push(&mut line_to_pos, l, pos, num_nodes);
            }
        }

        let mut intervals = LineIntervals::default();

        for (l, positions) in small_map_iter_mut(&mut line_to_pos) {
            positions.sort_unstable();
            let min = positions[0];
            let max = positions[positions.len() - 1];
            // Make sure that the positions are contiguous (i.e. match the
            // positions we'd expect on that line).
            let pos_iter = self.line_positions_from(min, l);
            if !positions.iter().zip(pos_iter).all(|(&p1, p2)| p1 == p2) {
                return None;
            }
            intervals.0.push((l, LineInterval { min, max }));
        }

        Some(intervals)
    }

    /// Shrink the memory allocated to scratch space for the
    /// [`LineConvexChecker::get_intervals`] method to the amount used during
    /// the last call to the method.
    pub fn shrink_to_fit(&mut self) {
        let mut line_to_pos = self.get_intervals_scratch_space.borrow_mut();
        line_to_pos.retain(|(l, vec)| {
            if l.is_none() || vec.is_empty() {
                return false;
            }
            vec.shrink_to_fit();
            true
        });
    }

    /// Get all positions starting from `start_pos` on the given line.
    #[inline(always)]
    fn line_positions_from(
        &self,
        start_pos: Position,
        line_index: LineIndex,
    ) -> impl Iterator<Item = Position> + '_ {
        let start = self
            .find_index(line_index, start_pos)
            .expect("start not on line");
        let line = &self.lines[line_index.as_usize()];

        line[start..].iter().map(|&n| self.get_position(n))
    }

    /// Binary search for the index of the first element in `line` with position
    /// equal to `min`.
    fn find_index(&self, line: LineIndex, Position(pos): Position) -> Option<usize> {
        let line = &self.lines[line.as_usize()];
        if line.is_empty() {
            return None;
        }
        let mut low = 0;
        let mut high = line.len() - 1;
        let Position(low_pos) = self.get_position(line[low]);
        let Position(high_pos) = self.get_position(line[high]);

        if low_pos == pos {
            return Some(low);
        } else if high_pos == pos {
            return Some(high);
        } else if low_pos > pos || high_pos < pos {
            return None;
        }

        // invariant: low_pos < pos < high_pos
        loop {
            let Position(low_pos) = self.get_position(line[low]);
            let Position(high_pos) = self.get_position(line[high]);

            // Normal binary search would use alpha = 1/2, but assuming the
            // positions are evenly distributed, we can use a better guess.
            let alpha = (pos - low_pos) as f64 / (high_pos - low_pos) as f64;
            let mut guess = low + (alpha * (high - low) as f64).round() as usize;

            // Ensure progress.
            if guess == low {
                guess += 1;
            } else if guess == high {
                guess -= 1;
            }

            let Position(guess_pos) = self.get_position(line[guess]);
            match guess_pos.cmp(&pos) {
                Ordering::Equal => return Some(guess),
                Ordering::Less => low = guess,
                Ordering::Greater => high = guess,
            }
        }
    }
}

#[inline(always)]
fn small_map_iter_mut(
    small_map: &mut SmallVec<[(Option<LineIndex>, Vec<Position>); 8]>,
) -> impl Iterator<Item = (LineIndex, &mut Vec<Position>)> + '_ {
    small_map.iter_mut().map_while(|(l, p)| Some(((*l)?, p)))
}

#[inline(always)]
fn small_map_push(
    small_map: &mut SmallVec<[(Option<LineIndex>, Vec<Position>); 8]>,
    key: LineIndex,
    value: Position,
    new_vec_capacity: usize,
) {
    // Find where to push `value`. In order of preference:
    // - at the existing entry for `key` in the map, or
    // - at the first pre-allocated but empty entry, or
    // - at a freshly allocated entry in the map.
    let ind = if let Some(i) = small_map
        .iter()
        .position(|&(ll, _)| ll == Some(key) || ll.is_none())
    {
        if small_map[i].0.is_none() {
            // Reuse an existing empty entry.
            small_map[i].0 = Some(key);
        }
        i
    } else {
        // Allocate a new entry.
        small_map.push((Some(key), Vec::with_capacity(new_vec_capacity)));
        small_map.len() - 1
    };
    small_map[ind].1.push(value);
}

#[inline(always)]
fn small_map_clear(small_map: &mut SmallVec<[(Option<LineIndex>, Vec<Position>); 8]>) {
    for (l, p) in small_map {
        *l = None;
        p.clear();
    }
}

/// Construct a closure that maintains a frontier of line ends as the lines
/// are getting constructed.
///
/// As nodes of the graph are considered in topological order, calls to the
/// closure will extend the lines to the new node and create new lines as
/// required.
fn extend_line_ends_frontier<G>(graph: &G) -> impl FnMut(NodeIndex) -> LinePositions + '_
where
    G: LinkView + Clone,
{
    // The current ends of all lines. The keys are always outgoing ports.
    let mut frontier: BTreeMap<PortIndex, LinePositions> = BTreeMap::new();
    // Total number of lines. Used to create new line indices.
    let mut n_lines = 0;

    /// Get a line and position at the given port on the frontier.
    fn pop_frontier(
        frontier: &mut BTreeMap<PortIndex, LinePositions>,
        port: PortIndex,
    ) -> Option<(LineIndex, Position)> {
        let positions = frontier.get_mut(&port)?;
        let Some(line_index) = positions.line_indices.pop() else {
            frontier.remove(&port);
            return None;
        };
        let position = positions.position;
        Some((line_index, position))
    }

    /// Add a line and position to the frontier for the given frontier port.
    fn push_frontier(
        frontier: &mut BTreeMap<PortIndex, LinePositions>,
        port: PortIndex,
        line_index: LineIndex,
        position: Position,
    ) {
        let entry = frontier.entry(port).or_default();
        entry.line_indices.push(line_index);
        entry.position = position;
    }

    move |node: NodeIndex| {
        // 1. Get lines to extend from the current frontier to node
        let incoming_ports = graph.inputs(node);
        // Map from incoming ports in `node` to lines that it will belong to
        // (once extended).
        let mut prev_lines: BTreeMap<_, _> = incoming_ports
            .map(|in_port| {
                let in_links = graph.port_links(in_port);
                let lines = in_links
                    .map(|(_, out_port)| {
                        pop_frontier(&mut frontier, out_port.into()).expect("unknown frontier port")
                    })
                    .collect_vec();
                (in_port, lines)
            })
            .collect();

        // 2. Compute
        //     - new position of `node` (max of all previous positions + 1, or zero)
        //     - lines that `node` will belong to (once extended). Note that we
        //       may need to add new lines to accomodate all outgoing links, see below.
        let position = prev_lines
            .values()
            .flat_map(|vec| vec.iter().map(|&(_, pos)| pos))
            .max()
            .map(|p| p.next())
            .unwrap_or_default();
        let mut lines: BTreeSet<_> = prev_lines
            .values()
            .flat_map(|vec| vec.iter().map(|&(line_index, _)| line_index))
            .collect();

        // 3. Reuse lines on incoming ports where possible and add new lines if
        // required, so that every outgoing port has as many lines as it is
        // connected to ports.
        for out_port in graph.outputs(node) {
            for _ in 0..graph.port_links(out_port).count() {
                let offset = graph.port_offset(out_port).unwrap().index();
                let in_port = graph.input(node, offset);
                if let Some((line_index, _)) = in_port
                    .and_then(|in_port| prev_lines.get_mut(&in_port))
                    .and_then(|v| v.pop())
                {
                    // We can extend an existing line.
                    push_frontier(&mut frontier, out_port, line_index, position);
                } else {
                    // We need to start a new line.
                    let new_line = LineIndex(n_lines);
                    push_frontier(&mut frontier, out_port, new_line, position);
                    lines.insert(new_line);
                    n_lines += 1;
                }
            }
        }

        // Isolated nodes will not be assigned to any lines: add a new line in
        // this case.
        if lines.is_empty() {
            let new_line = LineIndex(n_lines);
            lines.insert(new_line);
            n_lines += 1;
        }

        LinePositions {
            line_indices: lines.into_iter().collect(),
            position,
        }
    }
}

impl<G> ConvexChecker for LineConvexChecker<G>
where
    G: LinkView + Clone,
{
    fn is_convex(
        &self,
        nodes: impl IntoIterator<Item = NodeIndex>,
        inputs: impl IntoIterator<Item = PortIndex>,
        outputs: impl IntoIterator<Item = PortIndex>,
    ) -> bool {
        let pre_outputs: BTreeSet<_> = outputs
            .into_iter()
            .filter_map(|p| Some(self.graph.port_link(p)?.into()))
            .collect();
        if inputs.into_iter().any(|p| pre_outputs.contains(&p)) {
            return false;
        }
        self.is_node_convex(nodes)
    }
}

#[cfg(test)]
mod tests {
    use crate::{LinkMut, MultiPortGraph, PortMut};

    use super::*;

    use rstest::{fixture, rstest};

    /// Test DAG with always one input one output, but output may be connected to multiple inputs.
    ///
    /// There are furthermore two disjoint lines.
    ///
    /// ```text
    /// 0 -> 1 -> 2 -> 3
    ///        \- 4 -> 5
    ///         \- 6 -> 7
    /// 8 -> 9 -> 10
    /// ```
    #[fixture]
    fn two_lines_ish_graph() -> (MultiPortGraph, [NodeIndex; 11]) {
        let mut graph = MultiPortGraph::new();
        let nodes: Vec<NodeIndex> = (0..11).map(|_| graph.add_node(1, 1)).collect();
        let mut link = |n1, n2| graph.link_nodes(nodes[n1], 0, nodes[n2], 0).unwrap();
        link(0, 1);

        for i in (2..7).step_by(2) {
            link(1, i);
            link(i, i + 1);
        }

        link(8, 9);
        link(9, 10);

        (graph, nodes.try_into().unwrap())
    }

    /// ```text
    /// 0 --> 2
    /// 1 -/
    /// ```
    #[fixture]
    fn two_lines_merging_graph() -> (MultiPortGraph, [NodeIndex; 3]) {
        let mut graph = MultiPortGraph::new();
        let nodes: Vec<NodeIndex> = (0..3).map(|_| graph.add_node(1, 1)).collect();
        let mut link = |n1, n2| graph.link_nodes(nodes[n1], 0, nodes[n2], 0).unwrap();
        link(0, 2);
        link(1, 2);
        (graph, nodes.try_into().unwrap())
    }

    #[rstest]
    fn test_line_partition(two_lines_ish_graph: (MultiPortGraph, [NodeIndex; 11])) {
        let (graph, nodes) = two_lines_ish_graph;
        let checker = LineConvexChecker::new(graph);

        let node_n_is_at_position = |n: NodeIndex, (line_index, position): (usize, usize)| {
            assert_eq!(
                checker.get_position(n),
                Position(position as u32),
                "{n:?} is at position {:?}",
                Position(position as u32)
            );
            assert!(
                checker.get_lines(n).contains(&LineIndex(line_index as u32)),
                "{n:?} is on line {:?}",
                LineIndex(line_index as u32)
            );
        };

        let line0 = vec![nodes[0], nodes[1], nodes[6], nodes[7]];
        let line1 = vec![nodes[8], nodes[9], nodes[10]];
        let line2 = vec![nodes[1], nodes[4], nodes[5]];
        let line3 = vec![nodes[1], nodes[2], nodes[3]];

        // Line 0
        for (&n, pos) in line0.iter().zip(0..=3) {
            node_n_is_at_position(n, (0, pos));
        }

        // line 1
        for (&n, pos) in line1.iter().zip(0..=2) {
            node_n_is_at_position(n, (1, pos));
        }

        // Line 2
        for (&n, pos) in line2.iter().zip(1..=3) {
            node_n_is_at_position(n, (2, pos));
        }

        // Line 3
        for (&n, pos) in line3.iter().zip(1..=3) {
            node_n_is_at_position(n, (3, pos));
        }

        assert_eq!(checker.lines, [line0, line1, line2, line3]);
    }

    #[rstest]
    fn test_line_partition_merging(two_lines_merging_graph: (MultiPortGraph, [NodeIndex; 3])) {
        let (graph, nodes) = two_lines_merging_graph;
        let checker = LineConvexChecker::new(graph);

        let line0 = vec![nodes[0], nodes[2]];
        let line1 = vec![nodes[1], nodes[2]];

        assert_eq!(checker.lines, [line0, line1]);
    }

    #[rstest]
    fn test_try_extend_intervals(two_lines_ish_graph: (MultiPortGraph, [NodeIndex; 11])) {
        let (graph, nodes) = two_lines_ish_graph;
        let checker = LineConvexChecker::new(graph);

        let subgraph = (1..=4).map(|i| nodes[i]);
        let intervals = checker.get_intervals(subgraph.clone()).unwrap();

        let mut extended_intervals = LineIntervals::default();
        for node in subgraph {
            assert!(checker.try_extend_intervals(&mut extended_intervals, node));
        }
        assert_eq!(intervals, extended_intervals);
    }

    #[test]
    fn test_graph_line_partition() {
        let (g, [i1, i2, i3, n1, n2, o1, o2]) = super::super::tests::graph();
        let checker = LineConvexChecker::new(g);

        dbg!(checker.get_intervals([i1, n2, o1, n1]));

        assert!(checker.is_node_convex([i1, i2, i3]));
        assert!(checker.is_node_convex([i1, n2]));
        assert!(!checker.is_node_convex([i1, n2, o2]));
        assert!(!checker.is_node_convex([i1, n2, o1]));
        assert!(checker.is_node_convex([i1, n2, o1, n1]));
        assert!(checker.is_node_convex([i1, n2, o2, n1]));
        assert!(checker.is_node_convex([i1, i3, n2]));
        assert!(!checker.is_node_convex([i1, i3, o2]));
    }
}
