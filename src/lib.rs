use std::num::NonZeroU32;

//pub mod dot;
#[allow(clippy::module_inception)]
pub mod graph;
pub mod hierarchy;
pub mod substitute;
pub mod toposort;
pub mod unweighted;
pub mod weights;

#[cfg(feature = "pyo3")]
pub mod py_graph;

pub use crate::graph::PortGraph;
pub use crate::graph::{Graph, GraphMut};
pub use crate::unweighted::UnweightedGraph;

#[cfg_attr(feature = "pyo3", pyclass)]
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Direction {
    Incoming = 0,
    Outgoing = 1,
}

impl Default for Direction {
    #[inline(always)]
    fn default() -> Self {
        Direction::Incoming
    }
}

impl Direction {
    #[inline(always)]
    pub fn index(self) -> usize {
        self as usize
    }

    #[inline(always)]
    pub fn reverse(self) -> Direction {
        match self {
            Direction::Incoming => Direction::Outgoing,
            Direction::Outgoing => Direction::Incoming,
        }
    }
}

/// Incoming and outgoing.
pub const DIRECTIONS: [Direction; 2] = [Direction::Incoming, Direction::Outgoing];

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeIndex(NonZeroU32);

impl NodeIndex {
    #[inline]
    pub fn new(index: usize) -> Self {
        assert!(index < u32::MAX as usize);
        Self(unsafe { NonZeroU32::new_unchecked(1 + index as u32) })
    }

    #[inline]
    pub fn index(self) -> usize {
        u32::from(self.0) as usize - 1
    }
}

impl std::fmt::Debug for NodeIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // avoid unncessary newlines in alternate mode
        write!(f, "NodeIndex({})", self.index())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PortIndex(NonZeroU32);

impl PortIndex {
    #[inline]
    pub fn new(index: usize) -> Self {
        assert!(index < u32::MAX as usize);
        Self(unsafe { NonZeroU32::new_unchecked(1 + index as u32) })
    }

    #[inline]
    pub fn index(self) -> usize {
        u32::from(self.0) as usize - 1
    }
}

impl std::fmt::Debug for PortIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // avoid unnecessary newlines in alternate mode
        write!(f, "PortIndex({})", self.index())
    }
}

#[deprecated]
pub type EdgeIndex = (PortIndex, PortIndex);
