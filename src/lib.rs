#![warn(missing_docs)]
//! `portgraph` is a data structure library for graphs with node ports.
//!
//! A port graph (as implemented by this library) consists of a collection of
//! nodes, each equipped with an ordered sequence of input and output ports. A
//! port can be linked to exactly one other port of the opposite direction or be
//! left dangling.
//!
//! The core data structure [`PortGraph`] implements a port graph which
//! identifies nodes and ports via [`NodeIndex`] and [`PortIndex`] but does not
//! attach any additional information to them. To keep track of weights the user
//! of this library may accompany a [`PortGraph`] with a data structure which
//! maps from indices to the weight type such as a [`SecondaryMap`] or a
//! [`HashMap`]. This allows for more flexibility in how weights are stored and
//! managed, for instance optimizing for cache locality or sparsity. The
//! [`Weights`] struct offers a simple wrapper around two a [`SecondaryMap`]s to
//! quickly encode port and node weights together.
//!
//! Using the node and port indices also allows to impose additional structure
//! to a [`PortGraph`]. This is exemplified via [`Hierarchy`] which arranges a
//! port graph's nodes into a forest so that it can represent a port graph in
//! which nodes may be nested within each other.
//!
//! [`HashMap`]: std::collections::HashMap
//!
//! # Example
//!
//! ```
//! use portgraph::{PortGraph, Direction};
//! use portgraph::algorithms::toposort;
//! use portgraph::substitute::Rewrite;
//!
//! // Create a graph with two nodes, each with two input and two output ports
//! let mut graph = PortGraph::new();
//! let node_a = graph.add_node(2, 2);
//! let node_b = graph.add_node(2, 2);
//!
//! // Link the first output port of node A to the first input port of node B
//! graph.link_nodes(node_a, 0, node_b, 0).unwrap();
//!
//! // Get globally unique indices for the ports, and link them directly
//! let port_a = graph.output(node_a, 1).unwrap();
//! let port_b = graph.input(node_b, 1).unwrap();
//! graph.link_ports(port_a, port_b).unwrap();
//!
//! // Run a topological sort on the graph starting at node A.
//! let topo = toposort(&graph, [node_a], Direction::Outgoing);
//! assert_eq!(topo.collect::<Vec<_>>(), [node_a, node_b]);
//!
//! ```
//!
//! # Features
//!
//! - `serde` enables serialization and deserialization of `PortGraph`s and
//!   graph component structures.
//! - `pyo3` enables Python bindings.
//!
use std::num::{NonZeroU16, NonZeroU32};
use thiserror::Error;

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

pub mod algorithms;
pub mod dot;
pub mod hierarchy;
pub mod portgraph;
pub mod secondary;
pub mod substitute;
pub mod weights;

#[cfg(feature = "pyo3")]
pub mod py_graph;

#[cfg(feature = "proptest")]
pub mod proptest;

#[doc(inline)]
pub use crate::hierarchy::Hierarchy;
#[doc(inline)]
pub use crate::portgraph::{LinkError, PortGraph};
#[doc(inline)]
pub use crate::secondary::SecondaryMap;
#[doc(inline)]
pub use crate::weights::Weights;

/// Direction of a port.
#[cfg_attr(feature = "pyo3", pyclass)]
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord, Hash, Default)]
pub enum Direction {
    /// Input to a node.
    #[default]
    Incoming = 0,
    /// Output from a node.
    Outgoing = 1,
}

impl Direction {
    /// Incoming and outgoing directions.
    pub const BOTH: [Direction; 2] = [Direction::Incoming, Direction::Outgoing];

    /// Returns the opposite direction.
    #[inline(always)]
    pub fn reverse(self) -> Direction {
        match self {
            Direction::Incoming => Direction::Outgoing,
            Direction::Outgoing => Direction::Incoming,
        }
    }
}

impl From<Direction> for usize {
    #[inline(always)]
    fn from(dir: Direction) -> Self {
        dir as usize
    }
}

impl TryFrom<usize> for Direction {
    type Error = IndexError;

    #[inline(always)]
    fn try_from(dir: usize) -> Result<Self, Self::Error> {
        match dir {
            0 => Ok(Direction::Incoming),
            1 => Ok(Direction::Outgoing),
            index => Err(IndexError { index }),
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
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct NodeIndex(NonZeroU32);

impl NodeIndex {
    /// Maximum allowed index. The higher bit is reserved for efficient encoding of the port graph.
    const MAX: usize = (u32::MAX / 2) as usize - 1;

    /// Creates a new node index from a `usize`.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than `2^31 - 2`.
    #[inline]
    pub fn new(index: usize) -> Self {
        index.try_into().unwrap()
    }

    /// Returns the index as a `usize`.
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
        if index > Self::MAX {
            Err(IndexError { index })
        } else {
            // SAFETY: The value cannot be zero
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
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct PortIndex(NonZeroU32);

impl PortIndex {
    /// Maximum allowed index. The higher bit is reserved for efficient encoding of the port graph.
    const MAX: usize = (u32::MAX / 2) as usize - 1;

    /// Creates a new port index from a `usize`.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than `2^31 - 2`.
    #[inline]
    pub fn new(index: usize) -> Self {
        index.try_into().unwrap()
    }

    /// Returns the index as a `usize`.
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
        if index > Self::MAX {
            Err(IndexError { index })
        } else {
            // SAFETY: The value cannot be zero
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

/// Error indicating a `NodeIndex`, `PortIndex`, or `Direction` is too large.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[error("the index {index} is too large.")]
pub struct IndexError {
    index: usize,
}

/// Port offset in a node
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum PortOffset {
    /// Input to a node
    ///
    /// The index is shifted by one to allow the null pointer optimization.
    ///
    /// TODO: Check if this is actually necessary.
    Incoming(NonZeroU16),
    /// Output from a node.
    Outgoing(u16),
}

impl PortOffset {
    /// Creates a new port offset.
    #[inline(always)]
    pub fn new(direction: Direction, offset: usize) -> Self {
        match direction {
            Direction::Incoming => Self::new_incoming(offset),
            Direction::Outgoing => Self::new_outgoing(offset),
        }
    }

    /// Creates a new incoming port offset.
    #[inline(always)]
    pub fn new_incoming(offset: usize) -> Self {
        assert!(offset < u16::MAX as usize);
        // SAFETY: The value cannot be zero
        let offset = unsafe { NonZeroU16::new_unchecked(offset.saturating_add(1) as u16) };
        PortOffset::Incoming(offset)
    }

    /// Creates a new outgoing port offset.
    #[inline(always)]
    pub fn new_outgoing(offset: usize) -> Self {
        assert!(offset <= u16::MAX as usize);
        PortOffset::Outgoing(offset as u16)
    }

    /// Returns the direction of the port.
    #[inline(always)]
    pub fn direction(self) -> Direction {
        match self {
            PortOffset::Incoming(_) => Direction::Incoming,
            PortOffset::Outgoing(_) => Direction::Outgoing,
        }
    }

    /// Returns the offset of the port.
    #[inline(always)]
    pub fn index(self) -> usize {
        match self {
            PortOffset::Incoming(offset) => (offset.get() - 1) as usize,
            PortOffset::Outgoing(offset) => offset as usize,
        }
    }
}

impl Default for PortOffset {
    fn default() -> Self {
        PortOffset::new_outgoing(0)
    }
}

impl std::fmt::Debug for PortOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.direction() {
            Direction::Incoming => write!(f, "Incoming({})", self.index()),
            Direction::Outgoing => write!(f, "Outgoing({})", self.index()),
        }
    }
}
