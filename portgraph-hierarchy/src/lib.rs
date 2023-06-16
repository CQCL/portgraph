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
//! use portgraph::{PortGraph, Direction, PortView, LinkView};
//! use portgraph::algorithms::{toposort, TopoSort};
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
//! let topo: TopoSort = toposort(&graph, [node_a], Direction::Outgoing);
//! assert_eq!(topo.collect::<Vec<_>>(), [node_a, node_b]);
//! ```
//!
//! # Features
//!
//! - `serde` enables serialization and deserialization of `PortGraph`s and
//!   graph component structures.
//! - `pyo3` enables Python bindings.
//!
pub mod dot;
pub mod hierarchy;

#[doc(inline)]
pub use crate::hierarchy::Hierarchy;
