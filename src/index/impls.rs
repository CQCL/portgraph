//! Macro-implementations of the index traits.

use super::{Direction, IndexError, NodeIndex, PortIndex, PortOffset};
use std::num;

macro_rules! impl_int_index_type {
    ($type:ty, $count_type:ty) => {
        impl NodeIndex for $type {
            const MAX_NODE: usize = {
                assert!(<$type>::BITS <= usize::BITS);
                Self::MAX as usize
            };
            type NodeCountTy = $count_type;

            #[inline]
            fn node_as_usize(self) -> usize {
                self as usize
            }

            #[inline]
            fn try_node_from_usize(index: usize) -> Result<Self, IndexError> {
                if index > <Self as NodeIndex>::MAX_NODE {
                    Err(IndexError {
                        index,
                        max: <Self as NodeIndex>::MAX_NODE,
                    })
                } else {
                    Ok(index as Self)
                }
            }

            #[inline]
            fn node_count(count: usize) -> Self::NodeCountTy {
                count as $count_type
            }

            #[inline]
            fn node_count_as_usize(count: Self::NodeCountTy) -> usize {
                count as usize
            }
        }

        impl PortIndex for $type {
            const MAX_PORT: usize = {
                assert!(<$type>::BITS <= usize::BITS);
                Self::MAX as usize
            };
            type PortCountTy = $count_type;

            #[inline]
            fn port_as_usize(self) -> usize {
                self as usize
            }

            #[inline]
            fn try_port_from_usize(index: usize) -> Result<Self, IndexError> {
                if index > <Self as PortIndex>::MAX_PORT {
                    Err(IndexError {
                        index,
                        max: <Self as PortIndex>::MAX_PORT,
                    })
                } else {
                    Ok(index as Self)
                }
            }

            #[inline]
            fn port_count(count: usize) -> Self::PortCountTy {
                count as $count_type
            }

            #[inline]
            fn port_count_as_usize(count: Self::PortCountTy) -> usize {
                count as usize
            }
        }

        impl PortOffset for $type {
            const MAX_OFFSET: usize = {
                assert!(<$type>::BITS <= usize::BITS);
                Self::MAX as usize
            };
            type OffsetCountTy = $count_type;

            fn try_new(direction: Direction, offset: usize) -> Result<Self, IndexError> {
                const DIRECTION_BIT: u32 = <$type>::BITS - 1;
                const DIRECTION_MASK: $type = 1 << DIRECTION_BIT;
                const OFFSET_MASK: $type = DIRECTION_MASK - 1;
                if offset > Self::MAX_OFFSET {
                    return Err(IndexError {
                        index: offset,
                        max: <Self as PortOffset>::MAX_OFFSET,
                    });
                }
                let value = match direction {
                    Direction::Incoming => offset as $type,
                    Direction::Outgoing => (offset as $type) | DIRECTION_MASK,
                };
                Ok(value)
            }

            fn direction(self) -> Direction {
                const DIRECTION_BIT: u32 = <$type>::BITS - 1;
                const DIRECTION_MASK: $type = 1 << DIRECTION_BIT;
                if self & DIRECTION_MASK == 0 {
                    Direction::Incoming
                } else {
                    Direction::Outgoing
                }
            }

            fn index(self) -> usize {
                const DIRECTION_BIT: u32 = <$type>::BITS - 1;
                const DIRECTION_MASK: $type = 1 << DIRECTION_BIT;
                (self & !DIRECTION_MASK) as usize
            }

            fn port_offset_count(count: usize) -> Self::OffsetCountTy {
                count as $count_type
            }

            fn port_offset_count_as_usize(count: Self::OffsetCountTy) -> usize {
                count as usize
            }
        }
    };
}

macro_rules! impl_nonzero_index_type {
    ($type:ty, $count_type:ty) => {
        impl NodeIndex for $type {
            const MAX_NODE: usize = (<$type>::MAX.get() - 1) as usize;
            type NodeCountTy = $count_type;

            #[inline]
            fn node_as_usize(self) -> usize {
                (self.get() - 1) as usize
            }

            #[inline]
            fn try_node_from_usize(index: usize) -> Result<Self, IndexError> {
                if index > <Self as NodeIndex>::MAX_NODE {
                    Err(IndexError {
                        index,
                        max: <Self as NodeIndex>::MAX_NODE,
                    })
                } else {
                    // SAFETY: The value can never be zero
                    Ok(unsafe {
                        Self::new_unchecked((index.saturating_add(1)).try_into().unwrap())
                    })
                }
            }

            #[inline]
            fn node_count(count: usize) -> Self::NodeCountTy {
                count as $count_type
            }

            #[inline]
            fn node_count_as_usize(count: Self::NodeCountTy) -> usize {
                count as usize
            }
        }

        impl PortIndex for $type {
            const MAX_PORT: usize = (<$type>::MAX.get() - 1) as usize;
            type PortCountTy = $count_type;

            #[inline]
            fn port_as_usize(self) -> usize {
                (self.get() - 1) as usize
            }

            #[inline]
            fn try_port_from_usize(index: usize) -> Result<Self, IndexError> {
                if index > <Self as PortIndex>::MAX_PORT {
                    Err(IndexError {
                        index,
                        max: <Self as PortIndex>::MAX_PORT,
                    })
                } else {
                    // SAFETY: The value can never be zero
                    Ok(unsafe {
                        Self::new_unchecked((index.saturating_add(1)).try_into().unwrap())
                    })
                }
            }

            #[inline]
            fn port_count(count: usize) -> Self::PortCountTy {
                count as $count_type
            }

            #[inline]
            fn port_count_as_usize(count: Self::PortCountTy) -> usize {
                count as usize
            }
        }

        impl PortOffset for $type {
            const MAX_OFFSET: usize = (Self::MAX.get() >> 1).saturating_sub(1) as usize;
            type OffsetCountTy = $count_type;

            #[inline]
            fn try_new(direction: Direction, offset: usize) -> Result<Self, IndexError> {
                const DIRECTION_BIT: u32 = <$type>::BITS - 1;
                const DIRECTION_MASK: $type = <$type>::new(1 << DIRECTION_BIT).unwrap();
                const OFFSET_MASK: $type = DIRECTION_MASK - 1;
                if offset > Self::MAX_OFFSET {
                    return Err(IndexError {
                        index: offset,
                        max: <Self as PortOffset>::MAX_OFFSET,
                    });
                }
                // SAFETY: The value can never be zero
                let value =
                    unsafe { Self::new_unchecked((offset.saturating_add(1)).try_into().unwrap()) };
                let value = match direction {
                    Direction::Incoming => value,
                    Direction::Outgoing => value | DIRECTION_MASK,
                };
                Ok(value)
            }

            #[inline]
            fn direction(self) -> Direction {
                const DIRECTION_BIT: u32 = <$type>::BITS - 1;
                const DIRECTION_MASK: $type = <$type>::new(1 << DIRECTION_BIT).unwrap();
                if self.get() & DIRECTION_MASK == 0 {
                    Direction::Incoming
                } else {
                    Direction::Outgoing
                }
            }

            #[inline]
            fn index(self) -> usize {
                const DIRECTION_BIT: u32 = <$type>::BITS - 1;
                let direction_mask = 1 << DIRECTION_BIT;
                (self.get() & !direction_mask).saturating_sub(1) as usize
            }

            #[inline]
            fn port_offset_count(count: usize) -> Self::OffsetCountTy {
                count as $count_type
            }

            #[inline]
            fn port_offset_count_as_usize(count: Self::OffsetCountTy) -> usize {
                count as usize
            }
        }
    };
}

impl_int_index_type!(u8, u16);
impl_int_index_type!(u16, u32);
impl_int_index_type!(u32, u64);
impl_int_index_type!(u64, u128);
impl_int_index_type!(usize, u128);
impl_nonzero_index_type!(num::NonZeroU8, u8);
impl_nonzero_index_type!(num::NonZeroU16, u16);
impl_nonzero_index_type!(num::NonZeroU32, u32);
impl_nonzero_index_type!(num::NonZeroU64, u64);
impl_nonzero_index_type!(num::NonZeroUsize, usize);
