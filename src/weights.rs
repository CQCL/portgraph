//! A graph component that encodes node and port weights. For more complex
//! scenarios, it is recommended to use a [`SecondaryMap`].
//!
//! This is a simple wrapper around two [`SecondaryMap`] containers. It does not
//! keep track of key validity, and returns default values for missing keys. It
//! is intended to be used alongside [`PortGraph`].
//!
//! [`PortGraph`]: crate::portgraph::PortGraph
//! [`SecondaryMap`]: crate::SecondaryMap
//!
//! # Example
//!
//! ```
//! # use portgraph::{PortGraph, NodeIndex, PortIndex};
//! # use portgraph::weights::Weights;
//! let mut graph = PortGraph::new();
//! let mut weights = Weights::<usize, isize>::new();
//!
//! // The weights must be set manually.
//! let node = graph.add_node(2, 2);
//! let [in0, in1, ..] = graph.inputs(node).collect::<Vec<_>>()[..] else { unreachable!() };
//! let [out0, out1, ..] = graph.outputs(node).collect::<Vec<_>>()[..] else { unreachable!() };
//! weights[node] = 42;
//! weights[in1] = 2;
//! weights[out0] = -1;
//! weights[out1] = -2;
//!
//! /// Unset weights return the default value.
//! assert_eq!(weights[in0], 0);
//!
//! // Graph operations that modify the keys have callbacks to update the weights.
//! graph.set_num_ports(node, 1, 3, |old, op| {
//!     op.new_index().map(|new| weights.ports.swap(old, new));
//! });
//!
//! // The map does not track item removals, but the user can shrink it manually.
//! graph.remove_node(node);
//! weights.nodes.shrink_to(graph.node_count());
//! weights.ports.shrink_to(graph.port_count());
//!
//! ```

use std::ops::{Index, IndexMut};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::{NodeIndex, PortIndex, UnmanagedDenseMap};

/// Graph component that encodes node and port weights.
/// Based on two [`UnmanagedDenseMap`] containers.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct Weights<N, P> {
    /// Node weights.
    pub nodes: UnmanagedDenseMap<NodeIndex, N>,
    /// Port weights.
    pub ports: UnmanagedDenseMap<PortIndex, P>,
}

impl<N, P> Weights<N, P>
where
    N: Clone + Default,
    P: Clone + Default,
{
    /// Creates a new secondary map.
    ///
    /// This does not allocate any memory until a value is modified.
    #[inline]
    pub fn new() -> Self {
        Self {
            nodes: UnmanagedDenseMap::new(),
            ports: UnmanagedDenseMap::new(),
        }
    }

    /// Creates a new secondary map with specified capacity.
    #[inline]
    pub fn with_capacity(nodes: usize, ports: usize) -> Self {
        Self {
            nodes: UnmanagedDenseMap::with_capacity(nodes),
            ports: UnmanagedDenseMap::with_capacity(ports),
        }
    }
}

impl<N, P> Default for Weights<N, P>
where
    N: Clone + Default,
    P: Clone + Default,
{
    #[inline]
    fn default() -> Self {
        Self {
            nodes: UnmanagedDenseMap::new(),
            ports: UnmanagedDenseMap::new(),
        }
    }
}

impl<N, P> Index<NodeIndex> for Weights<N, P>
where
    N: Clone,
    P: Clone,
{
    type Output = N;

    fn index(&self, key: NodeIndex) -> &Self::Output {
        &self.nodes[key]
    }
}

impl<N, P> IndexMut<NodeIndex> for Weights<N, P>
where
    N: Clone,
    P: Clone,
{
    fn index_mut(&mut self, key: NodeIndex) -> &mut Self::Output {
        &mut self.nodes[key]
    }
}

impl<N, P> Index<PortIndex> for Weights<N, P>
where
    N: Clone,
    P: Clone,
{
    type Output = P;

    fn index(&self, key: PortIndex) -> &Self::Output {
        &self.ports[key]
    }
}

impl<N, P> IndexMut<PortIndex> for Weights<N, P>
where
    N: Clone,
    P: Clone,
{
    fn index_mut(&mut self, key: PortIndex) -> &mut Self::Output {
        &mut self.ports[key]
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_weights() {
        let mut weights = Weights::<usize, isize>::new();
        let node = NodeIndex::new(0);
        let port = PortIndex::new(0);

        assert_eq!(weights[node], 0);
        assert_eq!(weights[port], 0);

        weights[node] = 42;
        weights[port] = -1;

        assert_eq!(weights[node], 42);
        assert_eq!(weights[port], -1);
    }
}
