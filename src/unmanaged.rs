//! A dense key-value map used to store graph weights.
//!
//! This map does not track valid indices and does not allocate any memory until
//! a value is modified, returning references to the default value instead.
//!
//! This structure is intended to be used alongside [`PortGraph`], as it does
//! not keep track of the valid keys.
//!
//! For simple cases where the nodes and ports have a single weight each, see
//! [`Weights`].
//!
//! [`PortGraph`]: crate::portgraph::PortGraph
//! [`Weights`]: crate::weights::Weights
//!
//! # Example
//!
//! ```
//! # use portgraph::{PortGraph, NodeIndex, PortIndex};
//! # use portgraph::unmanaged::UnmanagedMap;
//!
//! let mut graph = PortGraph::new();
//! let mut node_weights = UnmanagedMap::<NodeIndex, usize>::new();
//! let mut port_weights = UnmanagedMap::<PortIndex, isize>::new();
//!
//! // The weights must be set manually.
//! let node = graph.add_node(2, 2);
//! let [in0, in1, ..] = graph.inputs(node).collect::<Vec<_>>()[..] else { unreachable!() };
//! let [out0, out1, ..] = graph.outputs(node).collect::<Vec<_>>()[..] else { unreachable!() };
//! node_weights[node] = 42;
//! port_weights[in1] = 2;
//! port_weights[out0] = -1;
//! port_weights[out1] = -2;
//!
//! /// Unset weights return the default value.
//! assert_eq!(port_weights[in0], 0);
//!
//! // Graph operations that modify the keys use callbacks to update the weights.
//! graph.set_num_ports(node, 1, 3, |old, new| {if let Some(new) = new {port_weights.swap(old, new);}});
//!
//! // The map does not track item removals, but the user can shrink the map manually.
//! graph.remove_node(node);
//! node_weights.shrink_to(graph.node_count());
//! port_weights.shrink_to(graph.port_count());
//!
//! ```

use std::{
    cmp::Ordering,
    iter::{Enumerate, FusedIterator},
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ops::{Index, IndexMut},
    slice,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::SecondaryMap;

/// A dense map from keys to values with default fallbacks.
///
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct UnmanagedMap<K, V> {
    data: Vec<V>,
    phantom: PhantomData<K>,
    default: V,
}

impl<K: PartialEq, V: PartialEq> PartialEq for UnmanagedMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        if self.default != other.default {
            return false;
        }
        let common_len = std::cmp::min(self.data.len(), other.data.len());
        self.data[..common_len] == other.data[..common_len]
            && self.data[common_len..].iter().all(|v| v == &self.default)
            && other.data[common_len..].iter().all(|v| v == &other.default)
    }
}

impl<K, V> UnmanagedMap<K, V>
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
        if capacity > self.data.capacity() {
            self.data.reserve(capacity - self.data.capacity());
            self.data.resize(capacity, self.default.clone());
        }
    }

    /// Reduces the capacity of the secondary map to `capacity`.
    /// Stored values higher than `capacity` are dropped.
    ///
    /// Does nothing when the capacity of the secondary map is already lower.
    pub fn shrink_to(&mut self, capacity: usize) {
        self.data.truncate(capacity);
        self.data.shrink_to_fit();
    }

    /// Returns the maximum index the secondary map can contain without allocating.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    /// Remove key `old` and optionally move to key `new`.
    ///
    /// This method is useful for rekey callbacks such as in
    /// [`PortGraph::set_num_ports`] and [`PortGraph::compact_nodes`].
    ///
    /// [`PortGraph::set_num_ports`]: crate::portgraph::PortGraph::set_num_ports
    /// [`PortGraph::compact_nodes`]: crate::portgraph::PortGraph::compact_nodes
    pub fn rekey(&mut self, old: K, new: Option<K>)
    where
        V: Default,
    {
        if old.into() < self.data.len() {
            let val = mem::take(self.get_mut(old));
            let Some(new) = new else { return };
            if new.into() >= self.data.len() {
                self.resize_for_get_mut(new.into() + 1);
            }
            self.data[new.into()] = val;
        } else {
            let Some(new) = new else { return };
            if new.into() < self.data.len() {
                self.data[new.into()] = Default::default();
            }
        }
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
        let mut ptrs: [MaybeUninit<*mut V>; N] = [MaybeUninit::uninit(); N];

        // NOTE: This is a quadratic check. That is not a problem for very small
        // `N` but it would be nice if it could be avoided. See
        // https://docs.rs/slotmap/latest/slotmap/struct.SlotMap.html#method.get_disjoint_mut
        // for a linear time implementation. Unfortunately their trick is not
        // applicable here since we do not have the extra tagging bit available.
        let data = self.data.as_mut_ptr();
        for (i, key) in keys.iter().enumerate() {
            if keys[(i + 1)..].iter().any(|other| key == other) {
                return None;
            }

            let offset = (*key).into();
            if offset >= self.data.len() {
                return None;
            }
            // SAFETY: The offset is within the bounds of the underlying array.
            let ptr: *mut V = unsafe { data.add(offset) };
            ptrs[i].write(ptr);
        }

        // SAFETY: The pointers come from valid borrows into the underlying
        // array and we have checked their disjointness.
        let refs = unsafe { ptrs.map(|p| &mut *p.assume_init()) };
        Some(refs)
    }

    /// Must be called with `len` greater than `self.data.len()`.
    #[cold]
    fn resize_for_get_mut(&mut self, len: usize) {
        self.data.resize(len, self.default.clone());
    }

    /// Swaps the values of two keys.
    ///
    /// Allocates more memory when necessary to fit the keys.
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

impl<K, V> Default for UnmanagedMap<K, V>
where
    K: Into<usize> + Copy,
    V: Clone + Default,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Index<K> for UnmanagedMap<K, V>
where
    K: Into<usize> + Copy,
    V: Clone,
{
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key)
    }
}

impl<K, V> IndexMut<K> for UnmanagedMap<K, V>
where
    K: Into<usize> + Copy,
    V: Clone,
{
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key)
    }
}

impl<K, V> SecondaryMap<K, V> for UnmanagedMap<K, V>
where
    K: Into<usize> + TryFrom<usize> + Copy,
    V: Clone + Default,
{
    type Iter<'a> = UnmanagedIter<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    /// Creates a new secondary map.
    ///
    /// This does not allocate any memory until a value is modified.
    #[inline]
    fn new() -> Self {
        Self::with_default(Default::default())
    }

    #[inline]
    fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_default(capacity, Default::default())
    }

    #[inline]
    fn default_value(&self) -> V {
        self.default.clone()
    }

    #[inline]
    fn ensure_capacity(&mut self, capacity: usize) {
        UnmanagedMap::ensure_capacity(self, capacity)
    }

    #[inline]
    fn shrink_to(&mut self, capacity: usize) {
        UnmanagedMap::shrink_to(self, capacity)
    }

    #[inline]
    fn resize(&mut self, new_len: usize) {
        match self.data.len().cmp(&new_len) {
            Ordering::Less => self.ensure_capacity(new_len),
            Ordering::Greater => self.shrink_to(new_len),
            _ => {}
        }
    }

    #[inline]
    fn capacity(&self) -> usize {
        UnmanagedMap::capacity(self)
    }

    #[inline]
    fn get(&self, key: K) -> &V {
        UnmanagedMap::get(self, key)
    }

    /// Sets the value at a `key`.
    ///
    /// When the value is not present, the secondary map is resized to accommodate it.
    /// To avoid frequent resizing, use [`SecondaryMap::ensure_capacity`] to keep the
    /// capacity of the secondary map in line with the size of the key space.
    #[inline]
    fn set(&mut self, key: K, val: V) {
        self[key] = val;
    }

    #[inline]
    fn take(&mut self, key: K) -> V {
        let default = self.default.clone();
        mem::replace(&mut self[key], default)
    }

    #[inline]
    fn rekey(&mut self, old: K, new: Option<K>) {
        UnmanagedMap::rekey(self, old, new)
    }

    #[inline]
    fn swap(&mut self, key0: K, key1: K) {
        UnmanagedMap::swap(self, key0, key1)
    }

    fn iter<'a>(&'a self) -> Self::Iter<'a>
    where
        K: 'a,
        V: 'a,
    {
        UnmanagedIter {
            iter: self.data.iter().enumerate(),
            phantom: std::marker::PhantomData,
        }
    }
}

/// Iterator over non-default entries of an unmanaged map.
#[derive(Debug, Clone)]
pub struct UnmanagedIter<'a, K, V> {
    iter: Enumerate<slice::Iter<'a, V>>,
    phantom: std::marker::PhantomData<K>,
}

impl<'a, K, V> Iterator for UnmanagedIter<'a, K, V>
where
    K: TryFrom<usize>,
{
    type Item = (K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|(key, value)| (key.try_into().ok().unwrap(), value))
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.iter
            .nth(n)
            .map(|(key, value)| (key.try_into().ok().unwrap(), value))
    }

    #[inline]
    fn count(self) -> usize {
        self.iter.count()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for UnmanagedIter<'a, K, V>
where
    K: TryFrom<usize>,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()
            .map(|(key, value)| (key.try_into().ok().unwrap(), value))
    }
}

impl<'a, K, V> FusedIterator for UnmanagedIter<'a, K, V> where K: TryFrom<usize> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_capacity() {
        let mut map: UnmanagedMap<usize, usize> = UnmanagedMap::new();

        assert_eq!(map.capacity(), 0);

        map.ensure_capacity(10);
        assert!(map.capacity() >= 10);

        let prev_capacity = map.capacity();
        map.ensure_capacity(5);
        assert_eq!(map.capacity(), prev_capacity);

        map.ensure_capacity(15);
        assert!(map.capacity() >= 15);

        map.shrink_to(5);
        assert!(map.capacity() >= 5);

        let prev_capacity = map.capacity();
        map.shrink_to(10);
        assert_eq!(map.capacity(), prev_capacity);
    }

    #[test]
    fn test_get_mut() {
        let mut map: UnmanagedMap<usize, i32> = UnmanagedMap::with_default(4);

        let value = map.get_mut(0);
        assert_eq!(value, &4);
        *value = 1;
        assert_eq!(map.get_mut(0), &1);

        let value = map.try_get_mut(10);
        assert_eq!(value, None);

        let value = map.get_mut(10);
        assert_eq!(value, &mut 4);
        *value = 2;
        assert_eq!(map.try_get_mut(10), Some(&mut 2));
    }

    #[test]
    fn test_get_disjoint_mut() {
        let mut map: UnmanagedMap<usize, i32> = UnmanagedMap::new();

        let values = map.get_disjoint_mut([0, 1, 2]);
        assert_eq!(values, Some([&mut 0, &mut 0, &mut 0]));
        let values = values.unwrap();
        *values[0] = 1;
        *values[1] = 2;
        *values[2] = 3;
        assert_eq!(
            map.get_disjoint_mut([0, 1, 2]),
            Some([&mut 1, &mut 2, &mut 3])
        );

        let values = map.get_disjoint_mut([0, 1, 0]);
        assert_eq!(values, None);
    }

    #[test]
    fn test_swap() {
        let mut map: UnmanagedMap<usize, i32> = UnmanagedMap::new();
        map[0] = 0x10;
        map[1] = 0x11;
        map[3] = 0x13;

        map.swap(0, 1);
        assert_eq!(map[0], 0x11);
        assert_eq!(map[1], 0x10);

        map.swap(10, 3);
        assert_eq!(map[3], 0);
        assert_eq!(map[10], 0x13);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn secondary_serialize() {
        let mut map: UnmanagedMap<usize, i32> = UnmanagedMap::new();
        assert_eq!(crate::portgraph::test::ser_roundtrip(&map), map);
        map[0] = 0x10;
        map[1] = 0x11;
        map[3] = 0x13;
        assert_eq!(crate::portgraph::test::ser_roundtrip(&map), map);
    }

    #[test]
    fn eq_ignores_defaults() {
        let mut a = UnmanagedMap::<usize, usize>::new();
        let mut b = UnmanagedMap::<usize, usize>::new();
        a[4] = 0;
        assert_eq!(a, b);
        b[42] = 0;
        assert_eq!(a, b);
        b[40] = 24;
        assert_ne!(a, b);
    }
}
