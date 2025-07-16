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
//! use ::portgraph::*;
//! use ::portgraph::algorithms::{toposort, TopoSort};
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
//! let topo: TopoSort<_> = toposort(&graph, [node_a], Direction::Outgoing);
//! assert_eq!(topo.collect::<Vec<_>>(), [node_a, node_b]);
//! ```
//!
//! # Features
//!
//! - `serde` enables serialization and deserialization of `PortGraph`s and
//!   graph component structures.
//! - `pyo3` enables Python bindings.
//!

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

pub mod algorithms;
pub mod boundary;
pub mod hierarchy;
pub mod index;
pub mod multiportgraph;
pub mod portgraph;
pub mod render;
pub mod secondary;
pub mod unmanaged;
pub mod view;
pub mod weights;

#[cfg(feature = "proptest")]
pub mod proptest;

#[doc(inline)]
pub use crate::hierarchy::Hierarchy;
#[doc(inline)]
pub use crate::index::{IndexError, NodeIndex, PortIndex, PortOffset};
#[doc(inline)]
pub use crate::multiportgraph::MultiPortGraph;
#[doc(inline)]
pub use crate::portgraph::{LinkError, PortGraph};
#[doc(inline)]
pub use crate::secondary::SecondaryMap;
#[doc(inline)]
pub use crate::unmanaged::UnmanagedDenseMap;
#[doc(inline)]
pub use crate::view::{LinkMut, LinkView, MultiMut, MultiView, PortMut, PortView};
#[doc(inline)]
pub use crate::weights::Weights;

/// Direction of a port.
#[cfg_attr(feature = "pyo3", pyclass(eq, eq_int))]
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord, Hash, Default)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
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
