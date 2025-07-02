//! Definitions for Port and Node indices.

mod impls;

use std::hash::Hash;
use thiserror::Error;

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Type used to refer to a node in a portgraph.
///
/// In general, we prefer these types to be `NonZero<T>`, or a similar type
/// which allows *null pointer optimization* for efficiency. In portgraph we
/// generally assume that `Option<NodeIndex>` takes as much space as a
/// `NodeIndex` by itself, and similarly for `PortIndex`.
pub trait NodeIndex: Copy + Clone + PartialEq + Eq + PartialOrd + Ord + Hash {
    /// Returns the maximum allowed node index, when using zero-based indexing.
    const MAX_NODE: usize;

    /// A type used to count the number of different node indices.
    ///
    /// It should be able to represent `NodeIndex::MAX_NODE + 1`.
    type NodeCountTy: Copy + Clone + std::fmt::Debug + PartialEq + Eq + PartialOrd + Ord + Hash;

    /// Returns the node index as a zero-based `usize`.
    ///
    /// This value is always less than or equal to [`Self::MAX`].
    fn node_as_usize(self) -> usize;

    /// Creates a new node index from a zero-based `usize`.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than [`Self::MAX`].
    #[inline]
    fn node_from_usize(index: usize) -> Self {
        Self::try_node_from_usize(index)
            .unwrap_or_else(|_| panic!("Node index out of bounds: {index}"))
    }

    /// Creates a new node index from a zero-based `usize`.
    ///
    /// # Error
    ///
    /// Returns an error if the index is greater than [`Self::MAX`].
    fn try_node_from_usize(index: usize) -> Result<Self, IndexError>;

    /// Print the node index in a human-readable, zero-indexed format.
    #[inline]
    fn fmt_node(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NodeIndex({})", self.node_as_usize())
    }

    /// Prints the node index in a human-readable, zero-indexed format.
    #[inline]
    fn node_string(&self) -> String {
        format!("NodeIndex({})", self.node_as_usize())
    }

    /// Creates a new node count of type [`Self::NodeCountTy`].
    fn node_count(count: usize) -> Self::NodeCountTy;

    /// Returns the value of a node count as a `usize`.
    fn node_count_as_usize(count: Self::NodeCountTy) -> usize;
}

/// Type used to refer to a port in a portgraph.
///
/// In general, we prefer these types to be `NonZero<T>`, or a similar type
/// which allows *null pointer optimization* for efficiency. In portgraph we
/// generally assume that `Option<NodeIndex>` takes as much space as a
/// `NodeIndex` by itself, and similarly for `PortIndex`.
pub trait PortIndex: Copy + Clone + PartialEq + Eq + PartialOrd + Ord + Hash {
    /// Returns the maximum allowed port index, when using zero-based indexing.
    const MAX_PORT: usize;

    /// A type used to count the number of different port indices.
    ///
    /// It should be able to represent `PortIndex::MAX_PORT + 1`.
    type PortCountTy: Copy + Clone + std::fmt::Debug + PartialEq + Eq + PartialOrd + Ord + Hash;

    /// Returns the port index as a zero-based `usize`.
    ///
    /// This value is always less than or equal to [`Self::MAX`].
    fn port_as_usize(self) -> usize;

    /// Creates a new port index from a zero-based `usize`.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than [`Self::MAX`].
    fn port_from_usize(index: usize) -> Self {
        Self::try_port_from_usize(index)
            .unwrap_or_else(|_| panic!("Port index out of bounds: {index}"))
    }

    /// Creates a new port index from a zero-based `usize`.
    ///
    /// # Error
    ///
    /// Returns an error if the index is greater than [`Self::MAX`].
    fn try_port_from_usize(index: usize) -> Result<Self, IndexError>;

    /// Print the port index in a human-readable, zero-indexed format.
    #[inline]
    fn fmt_port(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PortIndex({})", self.port_as_usize())
    }

    /// Prints the port index in a human-readable, zero-indexed format.
    #[inline]
    fn port_string(&self) -> String {
        format!("PortIndex({})", self.port_as_usize())
    }

    /// Creates a new port count of type [`Self::PortCountTy`].
    fn port_count(count: usize) -> Self::PortCountTy;

    /// Returns the value of a port count as a `usize`.
    fn port_count_as_usize(count: Self::PortCountTy) -> usize;
}

/// Port offset in a node.
///
/// These refer to the position of a port within a node's input or output ports.
pub trait PortOffset: Copy + Clone + PartialEq + Eq + PartialOrd + Ord + Hash {
    /// Returns the maximum allowed port offset, when using zero-based indexing.
    const MAX_OFFSET: usize;

    /// A type used to count the number of different port offsets.
    ///
    /// It should be able to represent `PortOffset::MAX_OFFSET + 1`.
    type OffsetCountTy: Copy + Clone + std::fmt::Debug + PartialEq + Eq + PartialOrd + Ord + Hash;

    /// Creates a new port offset.
    ///
    /// ## Errors
    ///
    /// Errors if the offset is greater than [`PortOffset::MAX`].
    fn try_new(direction: Direction, offset: usize) -> Result<Self, IndexError>;

    /// Creates a new port offset.
    ///
    /// ## Panics
    ///
    /// Panics if the offset is greater than [`PortOffset::MAX`].
    #[inline]
    fn new(direction: Direction, offset: usize) -> Self {
        Self::try_new(direction, offset)
            .unwrap_or_else(|_| panic!("Port offset out of bounds: {offset}"))
    }

    /// Creates a new incoming port offset.
    ///
    /// ## Errors
    ///
    /// Errors if the offset is greater than [`PortOffset::MAX`].
    #[inline(always)]
    fn try_new_incoming(offset: usize) -> Result<Self, IndexError> {
        Self::try_new(Direction::Incoming, offset)
    }

    /// Creates a new incoming port offset.
    ///
    /// ## Panics
    ///
    /// Errors if the offset is greater than [`PortOffset::MAX`].
    #[inline(always)]
    fn new_incoming(offset: usize) -> Self {
        Self::new(Direction::Incoming, offset)
    }

    /// Creates a new outgoing port offset.
    ///
    /// ## Errors
    ///
    /// Errors if the offset is greater than [`PortOffset::MAX`].
    #[inline(always)]
    fn try_new_outgoing(offset: usize) -> Result<Self, IndexError> {
        Self::try_new(Direction::Outgoing, offset)
    }

    /// Creates a new outgoing port offset.
    ///
    /// ## Panics
    ///
    /// Errors if the offset is greater than [`PortOffset::MAX`].
    fn new_outgoing(offset: usize) -> Self {
        Self::new(Direction::Outgoing, offset)
    }

    /// Returns the direction of the port.
    fn direction(self) -> Direction;

    /// Returns the offset of the port.
    ///
    /// This is a zero-based index, guaranteed to be less than or equal to
    /// [`PortOffset::MAX`].
    fn index(self) -> usize;

    /// Returns the opposite port offset.
    ///
    /// This maps `PortOffset::Incoming(x)` to `PortOffset::Outgoing(x)` and
    /// vice versa.
    #[inline(always)]
    fn opposite(&self) -> Self {
        match self.direction() {
            Direction::Incoming => Self::new_outgoing(self.index()),
            Direction::Outgoing => Self::new_incoming(self.index()),
        }
    }

    /// Print the port index in a human-readable, zero-indexed format.
    #[inline]
    fn fmt_port_offset(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.direction() {
            Direction::Incoming => write!(f, "Incoming({})", self.index()),
            Direction::Outgoing => write!(f, "Outgoing({})", self.index()),
        }
    }

    /// Prints the port index in a human-readable, zero-indexed format.
    #[inline]
    fn port_string_offset(&self) -> String {
        match self.direction() {
            Direction::Incoming => format!("Incoming({})", self.index()),
            Direction::Outgoing => format!("Outgoing({})", self.index()),
        }
    }

    /// Creates a new port offset count of type [`Self::OffsetCountTy`].
    fn port_offset_count(count: usize) -> Self::OffsetCountTy;

    /// Returns the value of a port offset count as a `usize`.
    fn port_offset_count_as_usize(count: Self::OffsetCountTy) -> usize;
}

/// Module defining serialization and deserialization methods for [`NodeIndex`].
///
/// Intended to be used with the serde's `serde(with = "module")` field attribute.
///
/// ### Example
/// ```
/// use serde::{Deserialize, Serialize};
/// use portgraph::NodeIndex;
///
/// #[derive(Serialize, Deserialize)]
/// struct T<Node> {
///    #[serde(bound = "Node: NodeIndex")]
///    #[serde(with = "portgraph::index::serialize_node")]
///    node: Node,
/// }
/// ```
#[cfg(feature = "serde")]
mod serialize_node {
    use super::NodeIndex;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    /// Serializes a `NodeIndex` as a `usize`.
    pub fn serialize<S, Node: NodeIndex>(index: &Node, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        index.node_as_usize().serialize(serializer)
    }

    /// Deserializes a `NodeIndex` from a `usize`.
    pub fn deserialize<'de, D, Node: NodeIndex>(deserializer: D) -> Result<Node, D::Error>
    where
        D: Deserializer<'de>,
    {
        usize::deserialize(deserializer).map(NodeIndex::node_from_usize)
    }
}

/// Module defining serialization and deserialization methods for [`PortIndex`].
///
/// Intended to be used with the serde's `serde(with = "module")` field attribute.
///
/// ### Example
/// ```
/// use serde::{Deserialize, Serialize};
/// use portgraph::PortIndex;
///
/// #[derive(Serialize, Deserialize)]
/// struct T<Port> {
///    #[serde(bound = "Port: PortIndex")]
///    #[serde(with = "portgraph::index::serialize_port")]
///    port: Port,
/// }
/// ```
#[cfg(feature = "serde")]
mod serialize_port {
    use super::PortIndex;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    /// Serializes a `PortIndex` as a `usize`.
    pub fn serialize<S, P: PortIndex>(index: &P, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        index.port_as_usize().serialize(serializer)
    }

    /// Deserializes a `PortIndex` from a `usize`.
    pub fn deserialize<'de, D, P: PortIndex>(deserializer: D) -> Result<P, D::Error>
    where
        D: Deserializer<'de>,
    {
        usize::deserialize(deserializer).map(PortIndex::port_from_usize)
    }
}

/// Module defining serialization and deserialization methods for [`PortOffset`].
///
/// Intended to be used with the serde's `serde(with = "module")` field attribute.
///
/// ### Example
/// ```
/// use serde::{Deserialize, Serialize};
/// use portgraph::PortOffset;
///
/// #[derive(Serialize, Deserialize)]
/// struct T<Offset> {
///    #[serde(bound = "Port: PortOffset")]
///    #[serde(with = "portgraph::index::serialize_port_offset")]
///    port_offset: Offset,
/// }
/// ```
#[cfg(feature = "serde")]
mod serialize_port_offset {
    use crate::index::PortOffset;
    use crate::Direction;

    use serde::{Deserializer, Serializer};

    /// Serializes a `PortIndex` as a `usize`.
    pub fn serialize<S, O: PortOffset>(offset: &O, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match offset.direction() {
            Direction::Incoming => {
                serializer.serialize_newtype_variant("PortOffset", 0, "Incoming", &offset.index())
            }
            Direction::Outgoing => {
                serializer.serialize_newtype_variant("PortOffset", 1, "Outgoing", &offset.index())
            }
        }
    }

    /// Deserializes a `PortIndex` from a `usize`.
    pub fn deserialize<'de, D, O: PortOffset>(deserializer: D) -> Result<O, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct Vis<O: PortOffset>(std::marker::PhantomData<O>);
        impl<'de, O: PortOffset> serde::de::Visitor<'de> for Vis<O> {
            type Value = O;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(formatter, "a port offset")
            }

            fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::EnumAccess<'de>,
            {
                use serde::de::VariantAccess;

                let (variant, value) = data.variant()?;
                match variant {
                    "Incoming" => {
                        let idx: usize = value.newtype_variant()?;
                        Ok(PortOffset::new_incoming(idx))
                    }
                    "Outgoing" => {
                        let idx: usize = value.newtype_variant()?;
                        Ok(PortOffset::new_outgoing(idx))
                    }
                    _ => Err(serde::de::Error::unknown_variant(
                        variant,
                        &["Incoming", "Outgoing"],
                    )),
                }
            }
        }

        deserializer.deserialize_enum(
            "PortOffset",
            &["Incoming", "Outgoing"],
            Vis(std::marker::PhantomData::<O>),
        )
    }
}

/// Error returned when trying to initialize a [`NodeIndex`], [`PortIndex`], or
/// [`Direction`] with an invalid index.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[error("The index {index} is too large. The maximum allowed index is {max}.")]
pub struct IndexError {
    index: usize,
    max: usize,
}

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
            index => Err(IndexError { index, max: 1 }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_opposite() {
        let incoming = <u16 as PortOffset>::new_incoming(5);
        let outgoing = <u16 as PortOffset>::new_outgoing(5);

        assert_eq!(incoming.opposite(), outgoing);
        assert_eq!(outgoing.opposite(), incoming);
    }
}
