//! Index types for nodes and ports.

use std::{fmt, mem, ops};

use thiserror::Error;

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::Direction;

/// Index of a node within a `PortGraph`.
///
/// For a bit field with n bits, the index value will be restricted to at
/// most `2^(n-1) - 1` . The all null value is reserved for null-pointer optimisation.
///
/// Use with one of `usize`, `u64`, `u32`, `u16` and `u8`. Choose the bit width
/// that suits your needs.
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "U: Serialize + Unsigned",
        deserialize = "U: Deserialize<'de> + Unsigned"
    ))
)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "pyo3", derive(IntoPyObject))]
pub struct NodeIndex<U = u32>(BitField<U>);

/// Index of a port within a `PortGraph`.
///
/// For an index type with n bits, the index value will be restricted to at
/// most `2^(n-1) - 1` . The all null value is reserved for null-pointer optimisation.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "U: Serialize + Unsigned",
        deserialize = "U: Deserialize<'de> + Unsigned"
    ))
)]
#[cfg_attr(feature = "pyo3", derive(IntoPyObject))]
pub struct PortIndex<U = u32>(BitField<U>);

// Wraps the BitField API for NodeIndex and PortIndex.
macro_rules! index_impls {
    ($name:ident) => {
        impl<U: Unsigned> $name<U> {
            /// Maximum allowed index.
            pub fn max_index() -> usize {
                BitField::<U>::max_index()
            }

            /// Creates a new index from a `usize`.
            ///
            /// # Panics
            ///
            /// Panics if the index is greater than `Self::MAX`.
            #[inline(always)]
            pub fn new(index: usize) -> Self {
                Self(BitField::new(index, false))
            }

            /// Returns the index as a `T`.
            #[inline(always)]
            pub fn index(&self) -> usize {
                self.0.index_unchecked()
            }
        }

        impl<U: Unsigned> TryFrom<usize> for $name<U> {
            type Error = IndexError;

            #[inline(always)]
            fn try_from(index: usize) -> Result<Self, Self::Error> {
                BitField::try_from(index).map(Self)
            }
        }

        impl<U: Unsigned> From<$name<U>> for usize {
            #[inline(always)]
            fn from(index: $name<U>) -> Self {
                Self::from(index.0)
            }
        }

        impl<U: Unsigned> std::fmt::Debug for $name<U> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                // avoid unnecessary newlines in alternate mode
                write!(f, concat!(stringify!($name), "({})"), self.index())
            }
        }

        impl<U: Unsigned> AsMut<$name<U>> for BitField<U> {
            fn as_mut(&mut self) -> &mut $name<U> {
                // safety: Index types are repr(transparent)
                unsafe { &mut *(self as *mut BitField<U> as *mut $name<U>) }
            }
        }
    };
}

index_impls!(NodeIndex);
index_impls!(PortIndex);

impl<U: Unsigned> Default for PortIndex<U> {
    fn default() -> Self {
        PortIndex::new(0)
    }
}

/// Equivalent to `Option<NodeIndex<U>>` but stored within the size of `U`.
///
/// Uses the spare bit flag of the NodeIndex to store the `None` case.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "U: Serialize + Unsigned",
        deserialize = "U: Deserialize<'de> + Unsigned"
    ))
)]
pub struct MaybeNodeIndex<U>(BitField<U>);

/// Equivalent to `Option<PortIndex<U>>` but stored within the size of `U`.
///
/// Uses the spare bit flag of the PortIndex to store the `None` case.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "U: Serialize + Unsigned",
        deserialize = "U: Deserialize<'de> + Unsigned"
    ))
)]
pub struct MaybePortIndex<U>(BitField<U>);

macro_rules! maybe_index_impls {
    ($maybe_index:ident, $index:ident) => {
        impl<U: Unsigned> $maybe_index<U> {
            /// Create a new maybe index from an optional index.
            pub fn new(value: Option<$index<U>>) -> Self {
                match value {
                    Some(value) => {
                        debug_assert!(!value.0.is_none(), "invalid index");
                        Self(value.0)
                    }
                    None => Self(BitField::new_none()),
                }
            }

            /// Convert the maybe index to an option.
            #[inline(always)]
            pub fn to_option(self) -> Option<$index<U>> {
                if self.0.is_none() {
                    None
                } else {
                    Some($index(self.0))
                }
            }

            /// Get a mutable reference to the index, if it is not `None`.
            #[inline(always)]
            pub fn as_mut(&mut self) -> Option<&mut $index<U>> {
                if self.is_none() {
                    None
                } else {
                    Some(self.0.as_mut())
                }
            }

            /// Whether `self` contains an index.
            #[inline(always)]
            pub fn is_some(self) -> bool {
                !self.is_none()
            }

            /// Whether `self` does not contain an index.
            #[inline(always)]
            pub fn is_none(self) -> bool {
                self.0.is_none()
            }

            /// Unwrap the index, panicking with the given message if `self` is
            /// `None`.
            #[inline(always)]
            pub fn expect(self, msg: &str) -> $index<U> {
                if self.is_none() {
                    panic!("{msg}");
                }
                $index(self.0)
            }

            /// Unwrap the index, panicking if `self` is `None`.
            #[inline(always)]
            pub fn unwrap(self) -> $index<U> {
                self.expect("unwrap called on None")
            }

            /// Move the value out of the maybe index, leaving a `None` in its place.
            #[inline(always)]
            pub fn take(&mut self) -> Self {
                mem::replace(self, None.into())
            }

            /// Replace the value in the maybe index with a new value.
            #[inline(always)]
            pub fn replace(&mut self, value: $index<U>) -> Self {
                mem::replace(self, value.into())
            }
        }

        impl<U: Unsigned> fmt::Debug for $maybe_index<U> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{:?}", self.to_option())
            }
        }

        impl<U: Unsigned> From<$index<U>> for $maybe_index<U> {
            #[inline(always)]
            fn from(index: $index<U>) -> Self {
                Self(index.0)
            }
        }

        impl<U: Unsigned> From<$maybe_index<U>> for Option<$index<U>> {
            #[inline(always)]
            fn from(maybe_index: $maybe_index<U>) -> Self {
                maybe_index.to_option()
            }
        }

        impl<U: Unsigned> From<Option<$index<U>>> for $maybe_index<U> {
            #[inline(always)]
            fn from(index: Option<$index<U>>) -> Self {
                Self::new(index)
            }
        }

        impl<U: Unsigned> Default for $maybe_index<U> {
            #[inline(always)]
            fn default() -> Self {
                Self(BitField::new_none())
            }
        }

        impl<U: Unsigned> IntoIterator for $maybe_index<U> {
            type Item = $index<U>;
            type IntoIter = std::option::IntoIter<Self::Item>;

            fn into_iter(self) -> Self::IntoIter {
                self.to_option().into_iter()
            }
        }
    };
}

maybe_index_impls!(MaybeNodeIndex, NodeIndex);
maybe_index_impls!(MaybePortIndex, PortIndex);

impl MaybeNodeIndex<u32> {
    /// The `None` value for `MaybeNodeIndex<u32>`.
    // TODO: Added here so that [`crate::Hierarchy::new`] may be const.
    pub const NONE: Self = Self(BitField(u32::MAX));
}

/// Port offset in a node.
///
/// For an index type with n bits, the index value will be restricted to at
/// most `2^(n-1) - 1` . The most significant bit is reserved to store the direction
/// of the offset, see [`PortOffset::direction`].
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "U: Serialize + Unsigned",
        deserialize = "U: Deserialize<'de> + Unsigned"
    ))
)]
pub struct PortOffset<U = u16>(BitField<U>);

impl<U: Unsigned> PortOffset<U> {
    /// Maximum allowed offset. One bit is reserved for the direction.
    pub fn max_offset() -> usize {
        BitField::<U>::max_index()
    }

    /// Creates a new port offset.
    #[inline(always)]
    pub fn new(direction: Direction, offset: usize) -> Self {
        Self(BitField::new(offset, direction == Direction::Outgoing))
    }

    /// Creates a new incoming port offset.
    #[inline(always)]
    pub fn new_incoming(offset: usize) -> Self {
        Self::new(Direction::Incoming, offset)
    }

    /// Creates a new outgoing port offset.
    #[inline(always)]
    pub fn new_outgoing(offset: usize) -> Self {
        Self::new(Direction::Outgoing, offset)
    }

    /// Returns the direction of the port.
    #[inline(always)]
    pub fn direction(self) -> Direction {
        if self.0.bit_flag().expect("invalid port offset") {
            Direction::Outgoing
        } else {
            Direction::Incoming
        }
    }

    /// Returns the offset of the port.
    #[inline(always)]
    pub fn index(self) -> usize {
        self.0.index().expect("invalid port offset")
    }

    /// Returns the opposite port offset.
    ///
    /// This maps `PortOffset::Incoming(x)` to `PortOffset::Outgoing(x)` and
    /// vice versa.
    #[inline(always)]
    pub fn opposite(&self) -> Self {
        Self(self.0.flip_bit_flag())
    }
}

impl<U: Unsigned> Default for PortOffset<U> {
    fn default() -> Self {
        PortOffset::new_outgoing(0)
    }
}

impl<U: Unsigned> std::fmt::Debug for PortOffset<U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.direction() {
            Direction::Incoming => write!(f, "Incoming({})", self.index()),
            Direction::Outgoing => write!(f, "Outgoing({})", self.index()),
        }
    }
}

/// Fields of bits that can be used for node and port indices. Stores an index
/// and a bit flag.
///
/// For a field of n bits, the range of the index is [0, 2^(n-1) - 1]. This
/// saves one value (U::MAX) to flag an invalid/unset index and one bit for
/// extra information, e.g. Direction.
///
/// Use with one of `usize`, `u64`, `u32`, `u16` and `u8`. Choose the bit width
/// that suits your needs.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "pyo3", derive(IntoPyObject))]
pub struct BitField<U>(U);

/// Trait for unsigned integer types.
///
/// This is a wrapper around the `num_traits::Unsigned`, along with additional
/// bit logic traits that are typically implemented for unsigned integer types.
///
/// Implementations are provided for `u8`, `u16`, `u32`, `u64`, and `usize`.
pub trait Unsigned:
    Copy
    + std::fmt::Debug
    + Ord
    + num_traits::Unsigned
    + num_traits::Bounded
    + num_traits::ToPrimitive
    + num_traits::FromPrimitive
    + ops::Shr<u8, Output = Self>
    + ops::Not<Output = Self>
    + ops::BitAnd<Output = Self>
    + ops::BitOr<Output = Self>
    + ops::BitXor<Output = Self>
{
}

impl Unsigned for u8 {}
impl Unsigned for u16 {}
impl Unsigned for u32 {}
impl Unsigned for u64 {}
impl Unsigned for usize {}
// leave out u128 on purpose (casts to usize will panic)

impl<U: Unsigned> BitField<U> {
    /// Create a new bit field with the given index and bit flag.
    #[inline(always)]
    fn new(index: usize, bit_flag: bool) -> Self {
        let u = U::from_usize(index).expect("index too large");
        let ret = Self(u);
        if bit_flag {
            ret.set_bit_flag()
        } else {
            ret
        }
    }

    /// Create a new unset bit field
    #[inline(always)]
    fn new_none() -> Self {
        Self(U::max_value())
    }

    /// Maximum allowed index.
    #[inline(always)]
    fn max_index() -> usize {
        (U::max_value()
            .to_usize()
            .expect("max value larger than usize")
            >> 1)
            - 1
    }

    /// Return the index stored in the bit field as a `usize`.
    ///
    /// Return `None` if the bit field is unset.
    #[inline(always)]
    fn index(self) -> Option<usize> {
        if self.is_none() {
            return None;
        }
        Some(self.index_unchecked())
    }

    /// Return the index stored in the bit field as a `usize`.
    ///
    /// Panics if the bit field is unset.
    #[inline(always)]
    fn index_unchecked(self) -> usize {
        (self.0 & !Self::msb_mask())
            .to_usize()
            .expect("index too large")
    }

    /// Set the index in the bit field leaving the bit flag unchanged.
    ///
    /// If the bit field is unset, the index is set to the given value and the
    /// bit flag is set to false.
    #[allow(unused)]
    #[inline(always)]
    fn set_index(self, index: usize) -> Self {
        let u = U::from_usize(index).expect("index too large");
        let msb = if self.is_none() {
            U::zero()
        } else {
            self.0 & Self::msb_mask()
        };
        Self(u | msb)
    }

    /// Return the bit flag stored in the bit field.
    #[inline(always)]
    fn bit_flag(self) -> Option<bool> {
        if self.is_none() {
            return None;
        }
        Some(self.0 & Self::msb_mask() != U::zero())
    }

    /// Set the bit flag in the bit field leaving the index unchanged.
    ///
    /// Panics if the bit field is unset.
    #[inline(always)]
    fn set_bit_flag(self) -> Self {
        assert!(!self.is_none(), "bit field is unset");

        let msb = self.0 | Self::msb_mask();
        Self(msb)
    }

    /// Unset the bit flag in the bit field leaving the index unchanged.
    ///
    /// Panics if the bit field is unset.
    #[allow(unused)]
    #[inline(always)]
    fn unset_bit_flag(self) -> Self {
        assert!(!self.is_none(), "bit field is unset");

        let msb = self.0 & !Self::msb_mask();
        Self(msb)
    }

    #[inline(always)]
    fn flip_bit_flag(self) -> Self {
        Self(self.0 ^ Self::msb_mask())
    }

    #[inline(always)]
    fn unpack(self) -> Option<(usize, bool)> {
        let ind = self.index()?;
        let flag = self.bit_flag()?;
        Some((ind, flag))
    }

    #[inline(always)]
    fn pack(data: Option<(usize, bool)>) -> Self {
        match data {
            Some((ind, flag)) => Self::new(ind, flag),
            None => Self::new_none(),
        }
    }

    #[inline(always)]
    fn msb_mask() -> U {
        U::max_value() - (U::max_value() >> 1)
    }

    /// Whether the bit field is unset.
    #[inline(always)]
    fn is_none(self) -> bool {
        self == Self::new_none()
    }
}

#[cfg(feature = "serde")]
impl<U: Serialize + Unsigned> Serialize for BitField<U> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.unpack().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, U: Unsigned + Deserialize<'de>> Deserialize<'de> for BitField<U> {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Deserialize::deserialize(deserializer).map(BitField::pack)
    }
}

impl<U: Unsigned> TryFrom<usize> for BitField<U> {
    type Error = IndexError;

    #[inline]
    fn try_from(index: usize) -> Result<Self, Self::Error> {
        if index > Self::max_index() {
            Err(IndexError { index })
        } else {
            Ok(Self::new(index, false))
        }
    }
}

impl<U: Unsigned> From<BitField<U>> for usize {
    #[inline]
    fn from(bit_field: BitField<U>) -> Self {
        bit_field.index().expect("invalid index")
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
    use super::*;

    #[test]
    fn test_opposite() {
        let incoming = PortOffset::<u16>::new_incoming(5);
        let outgoing = PortOffset::<u16>::new_outgoing(5);

        assert_eq!(incoming.opposite(), outgoing);
        assert_eq!(outgoing.opposite(), incoming);
    }

    use rstest::rstest;

    #[rstest]
    #[case(0u16, false)]
    #[case(1u16, false)]
    #[case(16u16, true)]
    fn test_create_bitfield(#[case] value: u16, #[case] flag: bool) {
        let idx = BitField::<u16>::new(value as usize, flag);
        assert_eq!(idx.index().unwrap(), value as usize);
        assert_eq!(idx.bit_flag().unwrap(), flag);

        let idx = idx.flip_bit_flag();
        assert_eq!(idx.bit_flag().unwrap(), !flag);

        let idx = idx.set_bit_flag();
        assert!(idx.bit_flag().unwrap());

        let idx = idx.unset_bit_flag();
        assert!(!idx.bit_flag().unwrap());

        let idx = idx.set_index(2 * value as usize);
        assert_eq!(idx.index().unwrap(), 2 * value as usize);
    }

    #[test]
    fn test_from_usize_overflow_error() {
        let value = u16::MAX >> 1;
        assert!(BitField::<u16>::try_from(value as usize).is_err());
    }

    #[test]
    fn test_bitfield_none() {
        let idx = BitField::<u16>::new_none();
        assert_eq!(idx.index(), None);
        assert_eq!(idx.bit_flag(), None);

        let idx = idx.set_index(1);
        assert_eq!(idx.index().unwrap(), 1);
        assert!(!idx.bit_flag().unwrap());
    }

    #[test]
    fn test_port_offset_direction_and_index() {
        // Test Incoming direction
        let idx = 42;
        let incoming = PortOffset::<u16>::new_incoming(idx);
        assert_eq!(incoming.direction(), Direction::Incoming);
        assert_eq!(incoming.index(), { idx });
        assert_eq!(format!("{incoming:?}"), "Incoming(42)");

        // Test Outgoing direction
        let idx2 = 99;
        let outgoing = PortOffset::<u16>::new_outgoing(idx2);
        assert_eq!(outgoing.direction(), Direction::Outgoing);
        assert_eq!(outgoing.index(), { idx2 });
        assert_eq!(format!("{outgoing:?}"), "Outgoing(99)");
    }
}
