use std::num::NonZeroU32;
use thiserror::Error;

pub mod algorithms;
pub mod dot;
#[allow(clippy::module_inception)]
pub mod graph;
pub mod hierarchy;
pub mod secondary;
pub mod substitute;
pub mod unweighted;
pub mod weights;

#[cfg(feature = "pyo3")]
pub mod py_graph;

pub use crate::graph::PortGraph;
pub use crate::graph::{Graph, GraphMut};
pub use crate::unweighted::{LinkError, UnweightedGraph};

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
        index.try_into().unwrap()
    }

    #[inline]
    pub fn index(self) -> usize {
        self.into()
    }
}

impl From<NodeIndex> for usize {
    #[inline]
    fn from(index: NodeIndex) -> Self {
        u32::from(index.0) as usize - 1
    }
}

impl TryFrom<usize> for NodeIndex {
    type Error = IndexError;

    #[inline]
    fn try_from(index: usize) -> Result<Self, Self::Error> {
        if index >= (u32::MAX / 2) as usize {
            Err(IndexError)
        } else {
            Ok(Self(unsafe { NonZeroU32::new_unchecked(1 + index as u32) }))
        }
    }
}

impl std::fmt::Debug for NodeIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // avoid unnecessary newlines in alternate mode
        write!(f, "NodeIndex({})", self.index())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PortIndex(NonZeroU32);

impl PortIndex {
    #[inline]
    pub fn new(index: usize) -> Self {
        index.try_into().unwrap()
    }

    #[inline]
    pub fn index(self) -> usize {
        self.into()
    }
}

impl From<PortIndex> for usize {
    #[inline]
    fn from(index: PortIndex) -> Self {
        u32::from(index.0) as usize - 1
    }
}

impl TryFrom<usize> for PortIndex {
    type Error = IndexError;

    #[inline]
    fn try_from(index: usize) -> Result<Self, Self::Error> {
        if index >= (u32::MAX / 2) as usize {
            Err(IndexError)
        } else {
            Ok(Self(unsafe { NonZeroU32::new_unchecked(1 + index as u32) }))
        }
    }
}

impl std::fmt::Debug for PortIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // avoid unnecessary newlines in alternate mode
        write!(f, "PortIndex({})", self.index())
    }
}

#[derive(Debug, Clone, Error)]
#[error("Index too large.")]
pub struct IndexError;
