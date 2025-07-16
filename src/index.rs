//! Index types for nodes and ports.

use delegate::delegate;
use thiserror::Error;

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::Direction;

/// Index type that can be used to index nodes and ports.
///
/// Currently, implementations are provided for `usize`, `u64`, `u32`, `u16`,
/// and `u8`. Choose the bit width that suits your needs.
pub trait Index: Copy {
    const MAX: usize;

    fn try_from_usize(index: usize) -> Result<Self, IndexError>;

    fn to_usize(self) -> usize;

    fn set_msb(self) -> Self;

    fn unset_msb(self) -> Self;

    fn msb(self) -> bool;

    fn flip_msb(self) -> Self {
        if self.msb() {
            self.unset_msb()
        } else {
            self.set_msb()
        }
    }
}

macro_rules! impl_index_for {
    ($ty:ty) => {
        impl Index for $ty {
            const MAX: usize = <$ty>::MAX as usize;

            fn try_from_usize(index: usize) -> Result<Self, IndexError> {
                if index > <Self as Index>::MAX {
                    Err(IndexError { index })
                } else {
                    Ok(index as Self)
                }
            }

            fn to_usize(self) -> usize {
                self as usize
            }

            fn set_msb(self) -> Self {
                self | (1 << (<$ty>::BITS - 1))
            }

            fn unset_msb(self) -> Self {
                self & !(1 << (<$ty>::BITS - 1))
            }

            fn msb(self) -> bool {
                self & (1 << (<$ty>::BITS - 1)) != 0
            }
        }
    };
}

impl_index_for!(usize);
impl_index_for!(u64);
impl_index_for!(u32);
impl_index_for!(u16);
impl_index_for!(u8);

/// Index of a node within a `PortGraph`.
///
/// For an index type with n bits, the index value will be restricted to at
/// most `2^n - 1` . The all null value is reserved for null-pointer optimisation.
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "T: Serialize + Index",
        deserialize = "T: Deserialize<'de> + Index"
    ))
)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "pyo3", derive(IntoPyObject))]
pub struct NodeIndex<T>(ShiftedIndex<T>);

/// Index of a port within a `PortGraph`.
///
/// For an index type with n bits, the index value will be restricted to at
/// most `2^n - 1` . The all null value is reserved for null-pointer optimisation.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "T: Serialize + Index",
        deserialize = "T: Deserialize<'de> + Index"
    ))
)]
#[cfg_attr(feature = "pyo3", derive(IntoPyObject))]
pub struct PortIndex<T>(ShiftedIndex<T>);

// Wraps the ShiftedIndex API for NodeIndex and PortIndex.
macro_rules! index_impls {
    ($name:ident) => {
        impl<T: Index> $name<T> {
            /// Maximum allowed index.
            const MAX: usize = ShiftedIndex::<T>::MAX;

            /// Creates a new index from a `usize`.
            ///
            /// # Panics
            ///
            /// Panics if the index is greater than `Self::MAX`.
            #[inline]
            pub fn new(index: usize) -> Self {
                Self(ShiftedIndex::new(index))
            }

            delegate! {
                to self.0 {
                    /// Returns the index as a `T`.
                    pub fn index(&self) -> usize;
                }
            }
        }

        impl<T: Index> TryFrom<usize> for $name<T> {
            type Error = IndexError;

            #[inline]
            fn try_from(index: usize) -> Result<Self, Self::Error> {
                ShiftedIndex::try_from(index).map(Self)
            }
        }

        impl<T: Index> From<$name<T>> for usize {
            #[inline]
            fn from(index: $name<T>) -> Self {
                Self::from(index.0)
            }
        }

        impl<T: Index> std::fmt::Debug for $name<T> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                // avoid unnecessary newlines in alternate mode
                write!(f, concat!(stringify!($name), "({})"), self.index())
            }
        }
    };
}

index_impls!(NodeIndex);
index_impls!(PortIndex);

impl<T: Index> Default for PortIndex<T> {
    fn default() -> Self {
        PortIndex::new(0)
    }
}

/// Port offset in a node.
///
/// For an index type with n bits, the index value will be restricted to at
/// most `2^(n-1)` . The most significant bit is reserved to store the direction
/// of the offset, see [`PortOffset::direction`].
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct PortOffset<T>(T);

impl<T: Index> PortOffset<T> {
    /// Maximum allowed offset. One bit is reserved for the direction.
    const MAX: usize = T::MAX >> 1;

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
        if offset > Self::MAX {
            panic!("the offset is too large.")
        }
        let offset = T::try_from_usize(offset).expect("smaller than allowed MAX value");
        Self(offset)
    }

    /// Creates a new outgoing port offset.
    #[inline(always)]
    pub fn new_outgoing(offset: usize) -> Self {
        if offset > Self::MAX {
            panic!("the offset is too large.")
        }
        let offset = T::try_from_usize(offset).expect("smaller than allowed MAX value");
        offset.set_msb(); // mark that this is an outgoing port
        Self(offset)
    }

    /// Returns the direction of the port.
    #[inline(always)]
    pub fn direction(self) -> Direction {
        if self.0.msb() {
            Direction::Outgoing
        } else {
            Direction::Incoming
        }
    }

    /// Returns the offset of the port.
    #[inline(always)]
    pub fn index(self) -> usize {
        let offset = self.0;
        offset.unset_msb().to_usize()
    }

    /// Returns the opposite port offset.
    ///
    /// This maps `PortOffset::Incoming(x)` to `PortOffset::Outgoing(x)` and
    /// vice versa.
    #[inline(always)]
    pub fn opposite(&self) -> Self {
        Self(self.0.flip_msb())
    }
}

impl<T: Index> Default for PortOffset<T> {
    fn default() -> Self {
        PortOffset::new_outgoing(0)
    }
}

impl<T: Index> std::fmt::Debug for PortOffset<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.direction() {
            Direction::Incoming => write!(f, "Incoming({})", self.index()),
            Direction::Outgoing => write!(f, "Outgoing({})", self.index()),
        }
    }
}

/// An index, stored as shifted by one.
///
/// The range of the index is [0, MAX - 1], but is represented internally by the
/// interval [1, MAX]. This allows the *null pointer optimization* so that the
/// compiler can represent `Option<ShiftedIndex<T>>` in as much space as `T` by
/// itself.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "pyo3", derive(IntoPyObject))]
struct ShiftedIndex<T>(T);

impl<T: Index> ShiftedIndex<T> {
    /// Maximum allowed index.
    const MAX: usize = T::MAX - 1;

    /// Returns the index as a `T`.
    pub fn index(&self) -> usize {
        self.0.to_usize() - 1
    }

    /// Creates a new node index from a `usize`.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than `Self::MAX`.
    #[inline]
    pub fn new(index: usize) -> Self {
        if index > Self::MAX {
            panic!("the index is too large.")
        }
        debug_assert!(index + 1 <= T::MAX);
        let index = T::try_from_usize(index + 1).expect("smaller than allowed MAX value");
        Self(index)
    }
}

#[cfg(feature = "serde")]
impl<T: Serialize + Index> Serialize for ShiftedIndex<T> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.index().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T: Index + Deserialize<'de>> Deserialize<'de> for ShiftedIndex<T> {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        usize::deserialize(deserializer).map(ShiftedIndex::new)
    }
}

impl<T: Index> TryFrom<usize> for ShiftedIndex<T> {
    type Error = IndexError;

    #[inline]
    fn try_from(index: usize) -> Result<Self, Self::Error> {
        if index > Self::MAX {
            Err(IndexError { index })
        } else {
            Ok(Self::new(index))
        }
    }
}

impl<T: Index> From<ShiftedIndex<T>> for usize {
    #[inline]
    fn from(index: ShiftedIndex<T>) -> Self {
        index.index()
    }
}

/// Error indicating a `NodeIndex`, `PortIndex`, or `Direction` is too large.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[error("the index {index} is too large.")]
pub struct IndexError {
    pub(crate) index: usize,
}

#[cfg(test)]
mod tests {
    use std::u16;

    use super::*;

    #[test]
    fn test_opposite() {
        let incoming = PortOffset::<u32>::new_incoming(5);
        let outgoing = PortOffset::<u32>::new_outgoing(5);

        assert_eq!(incoming.opposite(), outgoing);
        assert_eq!(outgoing.opposite(), incoming);
    }

    use rstest::rstest;

    #[rstest]
    #[case(0u16)]
    #[case(1u16)]
    #[case(16u16)]
    fn test_shifted_index_new_and_index_u16(#[case] value: u16) {
        let idx = ShiftedIndex::<u16>::new(value as usize);
        assert_eq!(idx.index(), value as usize);
        assert_eq!(idx.0, value + 1);
    }

    #[test]
    fn test_shifted_index_try_from_usize_error() {
        let value = u16::MAX;
        assert!(ShiftedIndex::<u16>::try_from(value as usize).is_err());
    }

    #[test]
    fn test_port_offset_direction_and_index() {
        // Test Incoming direction
        let idx = 42;
        let incoming = PortOffset::<u16>::new_incoming(idx);
        assert_eq!(incoming.direction(), Direction::Incoming);
        assert_eq!(incoming.index(), idx as usize);
        assert_eq!(format!("{:?}", incoming), "Incoming(42)");

        // Test Outgoing direction
        let idx2 = 99;
        let outgoing = PortOffset::<u16>::new_outgoing(idx2);
        assert_eq!(outgoing.direction(), Direction::Outgoing);
        assert_eq!(outgoing.index(), idx2 as usize);
        assert_eq!(format!("{:?}", outgoing), "Outgoing(99)");
    }
}
