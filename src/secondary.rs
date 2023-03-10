use std::{
    marker::PhantomData,
    mem::MaybeUninit,
    ops::{Index, IndexMut},
};

/// A dense map from keys to values with default fallbacks.
#[derive(Debug, Clone)]
pub struct SecondaryMap<K, V> {
    data: Vec<V>,
    phantom: PhantomData<K>,
    default: V,
}

impl<K, V> SecondaryMap<K, V>
where
    K: Into<usize> + Copy,
    V: Clone,
{
    /// Creates a new secondary map.
    ///
    /// This does not allocate any memory until a value is modified.
    #[inline]
    pub fn new() -> Self
    where
        V: Default,
    {
        Self::with_default(Default::default())
    }

    /// Creates a new secondary map, specifying the default element.
    ///
    /// This does not allocate any memory until a value is modified.
    #[inline]
    pub fn with_default(default: V) -> Self {
        Self {
            data: Vec::new(),
            phantom: PhantomData,
            default,
        }
    }

    /// Creates a new secondary map with specified capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self
    where
        V: Default,
    {
        Self::with_capacity_and_default(capacity, Default::default())
    }

    /// Creates a new secondary map with specified capacity and default element.
    #[inline]
    pub fn with_capacity_and_default(capacity: usize, default: V) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
            phantom: PhantomData,
            default,
        }
    }

    /// Increases the capacity of the secondary map to `capacity`.
    ///
    /// Does nothing when the capacity of the secondary map is already sufficient.
    pub fn ensure_capacity(&mut self, capacity: usize) {
        if let Some(additional) = self.data.capacity().checked_sub(capacity) {
            self.data.reserve(additional);
            self.data.resize(self.data.capacity(), self.default.clone());
        }
    }

    /// Returns the maximum index the secondary map can contain without allocating.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    /// Immutably borrows the value at a `key`.
    ///
    /// Returns a borrow of the default value when no value has been set for the `key`.
    #[inline]
    pub fn get(&self, key: K) -> &V {
        self.data.get(key.into()).unwrap_or(&self.default)
    }

    /// Mutably borrows the value at a `key`.
    ///
    /// When the value is not present, the secondary map is resized to accommodate it.
    /// To avoid frequent resizing, use [`SecondaryMap::ensure_capacity`] to keep the
    /// capacity of the secondary map in line with the size of the key space.
    #[inline]
    pub fn get_mut(&mut self, key: K) -> &mut V {
        let index = key.into();

        if index >= self.data.len() {
            self.resize_for_get_mut(index + 1);
        }

        &mut self.data[index]
    }

    /// Mutably borrows the value at a `key`.
    ///
    /// Returns `None` when the `key` is beyond the capacity of the secondary map.
    #[inline]
    pub fn try_get_mut(&mut self, key: K) -> Option<&mut V> {
        self.data.get_mut(key.into())
    }

    /// Mutably borrows the values of a disjoint list of keys.
    ///
    /// Returns `None` when two keys coincide.
    pub fn get_disjoint_mut<const N: usize>(&mut self, keys: [K; N]) -> Option<[&mut V; N]>
    where
        K: Eq,
    {
        // Ensure that there is enough capacity
        if let Some(max_index) = keys.iter().map(|i| (*i).into()).max() {
            if max_index >= self.data.len() {
                self.resize_for_get_mut(max_index + 1);
            }
        };

        // Collect pointers for all indices
        let mut ptrs: [MaybeUninit<*mut V>; N] = unsafe { MaybeUninit::uninit().assume_init() };

        // NOTE: This is a quadratic check. That is not a problem for very small
        // `N` but it would be nice if it could be avoided. See
        // https://docs.rs/slotmap/latest/slotmap/struct.SlotMap.html#method.get_disjoint_mut
        // for a linear time implementation. Unfortunately their trick is not
        // applicable here since we do not have the extra tagging bit available.
        for (i, key) in keys.iter().enumerate() {
            ptrs[i] = MaybeUninit::new(&mut self.data[(*key).into()]);

            if keys.iter().skip(i + 1).any(|other| key == other) {
                return None;
            }
        }

        // SAFETY: The pointers come from valid borrows into the underlying
        // array and we have checked their disjointness.
        Some(unsafe { std::mem::transmute_copy::<_, [&mut V; N]>(&keys) })
    }

    /// Must be called with `len` greater than `self.data.len()`.
    #[cold]
    fn resize_for_get_mut(&mut self, len: usize) {
        self.data.resize(len, self.default.clone());
    }

    /// Swaps the values of two keys.
    ///
    /// Allocates more memory when neccessary to fit the keys.
    #[inline]
    pub fn swap(&mut self, key0: K, key1: K) {
        let index0 = key0.into();
        let index1 = key1.into();
        let max_index = std::cmp::max(index0, index1);

        if max_index >= self.data.len() {
            self.resize_for_get_mut(max_index + 1);
        }

        self.data.swap(index0, index1);
    }
}

impl<K, V> Default for SecondaryMap<K, V>
where
    K: Into<usize> + Copy,
    V: Clone + Default,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Index<K> for SecondaryMap<K, V>
where
    K: Into<usize> + Copy,
    V: Clone,
{
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key)
    }
}

impl<K, V> IndexMut<K> for SecondaryMap<K, V>
where
    K: Into<usize> + Copy,
    V: Clone,
{
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key)
    }
}
