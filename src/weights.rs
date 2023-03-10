use std::ops::{Index, IndexMut};

use crate::{NodeIndex, PortIndex, SecondaryMap};

/// Graph component that encodes node and port weights.
/// Based on two [`SecondaryMap`] containers.
#[derive(Debug, Clone)]
pub struct Weights<N, P> {
    pub nodes: SecondaryMap<NodeIndex, N>,
    pub ports: SecondaryMap<PortIndex, P>,
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
            nodes: SecondaryMap::new(),
            ports: SecondaryMap::new(),
        }
    }

    /// Creates a new secondary map with specified capacity.
    #[inline]
    pub fn with_capacity(nodes: usize, ports: usize) -> Self {
        Self {
            nodes: SecondaryMap::with_capacity(nodes),
            ports: SecondaryMap::with_capacity(ports),
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
            nodes: SecondaryMap::new(),
            ports: SecondaryMap::new(),
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
