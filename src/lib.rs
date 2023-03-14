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
use std::num::NonZeroU32;
use thiserror::Error;

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

pub mod algorithms;
pub mod dot;
pub mod hierarchy;
pub mod portgraph;
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
pub struct NodeIndex(NonZeroU32);

impl NodeIndex {
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
        if index >= (u32::MAX / 2) as usize {
            Err(IndexError { index })
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
        if index >= (u32::MAX / 2) as usize {
            Err(IndexError { index })
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

/// Error indicating a `NodeIndex`, `PortIndex`, or `Direction` is too large.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[error("the index {index} is too large.")]
pub struct IndexError {
    index: usize,
}
