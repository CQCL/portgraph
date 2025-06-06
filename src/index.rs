//! Definitions for Port and Node indices.
use std::hash::Hash;
use std::num;
use thiserror::Error;

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Trait for types that can be used for [`NodeIndex`] and [`PortIndex`].
///
/// In general, we prefer these types to be `NonZero<T>`, or a similar type
/// which allows *null pointer optimization* for efficiency. In portgraph we
/// generally assume that `Option<NodeIndex>` takes as much space as a
/// `NodeIndex` by itself, and similarly for `PortIndex`.
pub trait IndexType: Copy + Clone + PartialEq + Eq + PartialOrd + Ord + Hash {
    /// Returns the index as a zero-based `usize`.
    ///
    /// This value is always less than or equal to [`Self::MAX`].
    fn get(self) -> usize;

    /// Creates a new index from a zero-based `usize`.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than [`Self::MAX`].
    fn new(index: usize) -> Self;

    /// Returns the maximum allowed index, when using zero-based indexing.
    const MAX: usize;
}

macro_rules! impl_int_index_type {
    ($type:ty) => {
        impl IndexType for $type {
            #[inline]
            fn get(self) -> usize {
                self as usize
            }

            #[inline]
            fn new(index: usize) -> Self {
                if index > <Self as IndexType>::MAX {
                    panic!("Index out of bounds: {}", index);
                }
                index as Self
            }

            const MAX: usize = Self::MAX as usize;
        }
    };
}
impl_int_index_type!(u8);
impl_int_index_type!(u16);
impl_int_index_type!(u32);
impl_int_index_type!(u64);
impl_int_index_type!(usize);

macro_rules! impl_nonzero_index_type {
    ($type:ty) => {
        impl IndexType for $type {
            #[inline]
            fn get(self) -> usize {
                (self.get() - 1) as usize
            }

            #[inline]
            fn new(index: usize) -> Self {
                if index > <Self as IndexType>::MAX {
                    panic!("Index out of bounds: {}", index);
                }
                // SAFETY: The value can never be zero
                unsafe { Self::new_unchecked((index.saturating_add(1)).try_into().unwrap()) }
            }

            const MAX: usize = (<$type>::MAX.get() - 1) as usize;
        }
    };
}
impl_nonzero_index_type!(num::NonZeroU8);
impl_nonzero_index_type!(num::NonZeroU16);
impl_nonzero_index_type!(num::NonZeroU32);
impl_nonzero_index_type!(num::NonZeroU64);
impl_nonzero_index_type!(num::NonZeroUsize);

/// Index of a node within a `PortGraph`.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "pyo3", derive(IntoPyObject))]
pub struct NodeIndex<N = num::NonZeroU32>(N);

#[cfg(feature = "serde")]
impl<N: IndexType> Serialize for NodeIndex<N> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.index().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, N: IndexType> Deserialize<'de> for NodeIndex<N> {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        usize::deserialize(deserializer).map(NodeIndex::new)
    }
}

impl<N: IndexType> NodeIndex<N> {
    /// Maximum allowed index.
    const MAX: usize = N::MAX;

    /// Creates a new node index from a `usize`.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than N's [`IndexType::MAX`].
    #[inline]
    pub fn new(index: usize) -> Self {
        Self(N::new(index))
    }

    /// Returns the index as a `usize`.
    #[inline]
    pub fn index(self) -> usize {
        self.0.get()
    }
}

impl<N: IndexType> From<NodeIndex<N>> for usize {
    #[inline]
    fn from(index: NodeIndex<N>) -> Self {
        index.0.get()
    }
}

impl<N: IndexType> TryFrom<usize> for NodeIndex<N> {
    type Error = IndexError;

    #[inline]
    fn try_from(index: usize) -> Result<Self, Self::Error> {
        if index > Self::MAX {
            Err(IndexError { index, max: N::MAX })
        } else {
            Ok(Self::new(index))
        }
    }
}

impl<N: IndexType> std::fmt::Debug for NodeIndex<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NodeIndex({})", self.index())
    }
}

impl<N: IndexType> Default for NodeIndex<N> {
    fn default() -> Self {
        NodeIndex::new(0)
    }
}

/// Index of a port within a `PortGraph`.
///
/// The internal representation should be a `NonZero<T>`, or a similar type
/// which allows *null pointer optimization*, so that `Option<PortIndex>` takes
/// as much space as a `PortIndex` by itself.
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "pyo3", derive(IntoPyObject))]
pub struct PortIndex<P: IndexType = num::NonZeroU32>(P);

#[cfg(feature = "serde")]
impl<P: IndexType> Serialize for PortIndex<P> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.index().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, P: IndexType> Deserialize<'de> for PortIndex<P> {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        usize::deserialize(deserializer).map(PortIndex::new)
    }
}

impl<P: IndexType> PortIndex<P> {
    /// Maximum allowed index.
    const MAX: usize = P::MAX;

    /// Creates a new port index from a `usize`.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than P's [`IndexType::MAX`].
    #[inline]
    pub fn new(index: usize) -> Self {
        Self(P::new(index))
    }

    /// Returns the index as a `usize`.
    #[inline]
    pub fn index(self) -> usize {
        self.0.get()
    }
}

impl<P: IndexType> From<PortIndex<P>> for usize {
    #[inline]
    fn from(index: PortIndex<P>) -> Self {
        index.0.get()
    }
}

impl<P: IndexType> TryFrom<usize> for PortIndex<P> {
    type Error = IndexError;

    #[inline]
    fn try_from(index: usize) -> Result<Self, Self::Error> {
        if index > Self::MAX {
            Err(IndexError { index, max: P::MAX })
        } else {
            Ok(Self::new(index))
        }
    }
}

impl<P: IndexType> std::fmt::Debug for PortIndex<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PortIndex({})", self.index())
    }
}

impl<P: IndexType> Default for PortIndex<P> {
    fn default() -> Self {
        PortIndex::new(0)
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

/// Port offset in a node.
///
/// These refer to the position of a port within a node's input or output ports.
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct PortOffset<O: IndexType = u16> {
    index: O,
    direction: Direction,
}

impl<O: IndexType> PortOffset<O> {
    /// Creates a new port offset.
    ///
    /// ## Panics
    ///
    /// Panics if the offset is greater than O's [`IndexType::MAX`].
    #[inline(always)]
    pub fn new(direction: Direction, offset: O) -> Self {
        match direction {
            Direction::Incoming => Self::new_incoming(offset),
            Direction::Outgoing => Self::new_outgoing(offset),
        }
    }

    /// Creates a new incoming port offset.
    ///
    /// ## Panics
    ///
    /// Panics if the offset is greater than O's [`IndexType::MAX`].
    #[inline(always)]
    pub fn new_incoming(offset: O) -> Self {
        Self {
            index: offset,
            direction: Direction::Incoming,
        }
    }

    /// Creates a new outgoing port offset.
    ///
    /// ## Panics
    ///
    /// Panics if the offset is greater than O's [`IndexType::MAX`].
    #[inline(always)]
    pub fn new_outgoing(offset: O) -> Self {
        Self {
            index: offset,
            direction: Direction::Outgoing,
        }
    }

    /// Returns the direction of the port.
    #[inline(always)]
    pub fn direction(self) -> Direction {
        self.direction
    }

    /// Returns the offset of the port.
    ///
    /// This is a zero-based index, guaranteed to be less than or equal to
    /// O's [`IndexType::MAX`].
    #[inline(always)]
    pub fn index(self) -> usize {
        self.index.get()
    }

    /// Returns the opposite port offset.
    ///
    /// This maps `PortOffset::Incoming(x)` to `PortOffset::Outgoing(x)` and
    /// vice versa.
    #[inline(always)]
    pub fn opposite(&self) -> Self {
        Self {
            index: self.index,
            direction: self.direction.reverse(),
        }
    }
}

#[cfg(feature = "serde")]
impl<O: IndexType> Serialize for PortOffset<O> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self.direction {
            Direction::Incoming => {
                serializer.serialize_newtype_variant("PortOffset", 0, "Incoming", &self.index.get())
            }
            Direction::Outgoing => {
                serializer.serialize_newtype_variant("PortOffset", 1, "Outgoing", &self.index.get())
            }
        }
    }
}

#[cfg(feature = "serde")]
impl<'de, O: IndexType> Deserialize<'de> for PortOffset<O> {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct Vis<O: IndexType>(std::marker::PhantomData<O>);
        impl<'de, O: IndexType> serde::de::Visitor<'de> for Vis<O> {
            type Value = PortOffset<O>;

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
                        Ok(PortOffset::new_incoming(O::new(idx)))
                    }
                    "Outgoing" => {
                        let idx: usize = value.newtype_variant()?;
                        Ok(PortOffset::new_outgoing(O::new(idx)))
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

impl<O: IndexType> Default for PortOffset<O> {
    fn default() -> Self {
        PortOffset::new_outgoing(O::new(0))
    }
}

impl<O: IndexType> std::fmt::Debug for PortOffset<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.direction {
            Direction::Incoming => write!(f, "Incoming({})", self.index.get()),
            Direction::Outgoing => write!(f, "Outgoing({})", self.index.get()),
        }
    }
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
        let incoming = PortOffset::new_incoming(5u16);
        let outgoing = PortOffset::new_outgoing(5u16);

        assert_eq!(incoming.opposite(), outgoing);
        assert_eq!(outgoing.opposite(), incoming);
    }
}
