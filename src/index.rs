pub trait EntityIndex: Copy + Eq + Default {
    fn new(index: usize) -> Self {
        Self::try_new(index).unwrap()
    }

    fn try_new(index: usize) -> Option<Self>;
    fn index(self) -> usize;
}

#[macro_export]
macro_rules! make_entity {
    ($($(#[$attr:meta])* $vis:vis struct $name:ident(u32);)*) => { $(
        #[repr(transparent)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        $(#[$attr:meta])*
        $vis struct $name(::std::num::NonZeroU32);

        impl $crate::index::EntityIndex for $name {
            fn try_new(index: usize) -> Option<Self> {
                if index < u32::MAX as usize {
                    let index = index.wrapping_add(1) as u32;
                    Some(Self(unsafe {
                        ::std::num::NonZeroU32::new_unchecked(index)
                    }))
                } else {
                    None
                }
            }

            #[inline(always)]
            fn index(self) -> usize {
                u32::from(self.0).wrapping_sub(1) as usize
            }
        }

        impl ::std::default::Default for $name {
            fn default() -> Self {
                Self(::std::num::NonZeroU32::new(u32::MAX).unwrap())
            }
        }

    )*};
}

macro_rules! int_entity_impl {
    ($entity:ident) => {
        impl $crate::index::EntityIndex for $entity {
            #[inline(always)]
            fn try_new(ix: usize) -> Option<Self> {
                if (ix <= <$entity>::MAX as usize || <$entity>::BITS > usize::BITS) {
                    Some(ix as $entity)
                } else {
                    None
                }
            }

            #[inline(always)]
            fn index(self) -> usize {
                self as usize
            }
        }
    };
}

int_entity_impl!(u128);
int_entity_impl!(u64);
int_entity_impl!(u32);
int_entity_impl!(u16);
int_entity_impl!(u8);

make_entity! {
    pub struct NodeIndex(u32);
    pub struct PortIndex(u32);
}
