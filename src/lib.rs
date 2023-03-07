//! `portgraph` is a data structure library for graphs with ports.
//!
//! A port graph (as implemented by this library) consists of a collection of nodes,
//! each equipped with an ordered sequence of input and output ports.
//! A port can be linked to exactly one other port of the opposite direction or be left dangling.
//!
//! The core data structure [`PortGraph`] implements a port graph which identifies nodes and ports via
//! [`NodeIndex`] and [`PortIndex`] but does not attach any additional information to them.
//! To keep track of weights the user of this library may accompany a [`PortGraph`] with a data structure
//! which maps from indices to the weight type such as a [`SecondaryMap`] or a [`HashMap`].
//! This allows for more flexibility in how weights are stored and managed, for instance optimizing for
//! cache locality or sparsity.
//! Using the node and port indices also allows to impose additional structure to a [`PortGraph`].
//! This is exemplified via [`Hierarchy`] which arranges a port graph's nodes into a forest so that
//! it can represent a port graph in which nodes may be nested within each other.
//!
//! [`HashMap`]: std::collections::HashMap
use std::num::NonZeroU32;
use thiserror::Error;

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

pub mod algorithms;
pub mod dot;
pub mod hierarchy;
pub mod portgraph;
//pub mod py_graph;
pub mod secondary;
pub mod substitute;
pub mod weights;

#[cfg(feature = "pyo3")]
pub mod py_graph;

#[doc(inline)]
pub use crate::hierarchy::Hierarchy;
#[doc(inline)]
pub use crate::portgraph::{LinkError, PortGraph};
#[doc(inline)]
pub use crate::secondary::SecondaryMap;
#[doc(inline)]
pub use crate::weights::Weights;

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
    /// Incoming and outgoing.
    pub const BOTH: [Direction; 2] = [Direction::Incoming, Direction::Outgoing];

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

/// Index of a node within a `PortGraph`.
///
/// Restricted to be at most `2^31 - 1` to allow more efficient encodings of the port graph structure.
/// This type admits the *null pointer optimization* so that `Option<NodeIndex>` takes as much space
/// as a `NodeIndex` by itself.
#[repr(transparent)]
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

/// Index of a port within a `PortGraph`.
///
/// Restricted to be at most `2^31 - 1` to allow more efficient encodings of the port graph structure.
/// This type admits the *null pointer optimization* so that `Option<PortIndex>` takes as much space
/// as a `PortIndex` by itself.
#[repr(transparent)]
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

/// Error indicating a `NodeIndex` or `PortIndex` is too large.
#[derive(Debug, Clone, Error)]
#[error("Index too large.")]
pub struct IndexError;
