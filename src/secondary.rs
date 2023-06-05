//! TODO

use std::iter::FusedIterator;

use bitvec::{
    slice::{BitSlice, IterOnes},
    vec::BitVec,
};

/// A map from keys to values that does not manage it's indices.
///
/// Querying a key that has not been set returns a default value.
pub trait SecondaryMap<K, V> {
    /// An iterator over the non-default entries of the secondary map.
    type Iter<'a>: Iterator<Item = (K, &'a V)> + 'a
    where
        Self: 'a,
        K: 'a,
        V: 'a;

    /// Creates a new secondary map.
    fn new() -> Self;

    /// Creates a new secondary map with specified capacity.
    fn with_capacity(capacity: usize) -> Self;

    /// Returns the default value for the secondary map.
    /// Any key that has not been set will return this value.
    fn default_value(&self) -> V;

    /// Increases the capacity of the secondary map to `capacity`.
    fn ensure_capacity(&mut self, capacity: usize);

    /// Resizes the secondary map to `new_len`.
    fn resize(&mut self, new_len: usize);

    /// Returns the maximum index the secondary map can contain without allocating.
    fn capacity(&self) -> usize;

    /// Immutably borrows the value at a `key`.
    ///
    /// Returns a borrow of the default value when no value has been set for the `key`.
    fn get(&self, key: K) -> &V;

    /// Sets the value at a `key`.
    fn set(&mut self, key: K, val: V);

    /// Takes the value at a `key`, leaving `default()` behind.
    #[must_use = "Use `SecondaryMap::remove` if the stored value is not needed."]
    fn take(&mut self, key: K) -> V;

    /// Removes the value at a `key`, leaving `default()` behind.
    #[inline]
    fn remove(&mut self, key: K) {
        let _ = self.take(key);
    }

    /// Remove key `old` and optionally move to key `new`.
    ///
    /// This method is useful for rekey callbacks such as in
    /// [`PortGraph::set_num_ports`] and [`PortGraph::compact_nodes`].
    ///
    /// [`PortGraph::set_num_ports`]: crate::portgraph::PortGraph::set_num_ports
    /// [`PortGraph::compact_nodes`]: crate::portgraph::PortGraph::compact_nodes
    fn rekey(&mut self, old: K, new: Option<K>);

    /// Swaps the values of two keys.
    fn swap(&mut self, key0: K, key1: K);

    /// Returns an iterator over the non-default entries of the secondary map.
    fn iter<'a>(&'a self) -> Self::Iter<'a>
    where
        K: 'a,
        V: 'a;
}

impl<K> SecondaryMap<K, bool> for BitVec
where
    K: Into<usize> + TryFrom<usize>,
{
    type Iter<'a> = BitVecIter<'a, K> where Self: 'a, K: 'a;

    #[inline]
    fn new() -> Self {
        BitVec::new()
    }

    #[inline]
    fn with_capacity(capacity: usize) -> Self {
        BitVec::with_capacity(capacity)
    }

    #[inline]
    fn default_value(&self) -> bool {
        false
    }

    #[inline]
    fn ensure_capacity(&mut self, capacity: usize) {
        BitVec::reserve(self, capacity.saturating_sub(self.capacity()));
    }

    #[inline]
    fn resize(&mut self, new_len: usize) {
        BitVec::resize(self, new_len, false)
    }

    #[inline]
    fn capacity(&self) -> usize {
        BitVec::capacity(self)
    }

    #[inline]
    fn get(&self, key: K) -> &bool {
        // We can't return a reference to the internal bitflags, so we have to
        // create static bools.
        if BitSlice::get(self, key.into()).map_or(false, |f| *f) {
            &true
        } else {
            &false
        }
    }

    #[inline]
    fn set(&mut self, key: K, val: bool) {
        let key = key.into();
        if key >= BitVec::len(self) {
            if val {
                BitVec::resize(self, key + 1, false);
                BitSlice::set(self, key, true);
            }
        } else {
            BitSlice::set(self, key, val);
        }
    }

    #[inline]
    fn take(&mut self, key: K) -> bool {
        let key = key.into();
        if key < BitVec::len(self) {
            BitSlice::replace(self, key, false)
        } else {
            false
        }
    }

    #[inline]
    fn rekey(&mut self, old: K, new: Option<K>) {
        let val = self.take(old);
        if let Some(new) = new {
            self.set(new, val);
        }
    }

    #[inline]
    fn swap(&mut self, key0: K, key1: K) {
        let key0: usize = key0.into();
        let key1: usize = key1.into();
        let val0 = *self.get(key0);
        let val1 = *self.get(key1);
        if val0 != val1 {
            self.set(key0, val1);
            self.set(key1, val0);
        }
    }

    #[inline]
    fn iter<'a>(&'a self) -> Self::Iter<'a>
    where
        K: 'a,
    {
        BitVecIter {
            iter: BitSlice::iter_ones(self),
            phantom: std::marker::PhantomData,
        }
    }
}

/// Iterator over non-default entries of a bit vector secondary map.
#[derive(Debug, Clone, Default)]
pub struct BitVecIter<'a, K> {
    iter: IterOnes<'a, usize, bitvec::order::Lsb0>,
    phantom: std::marker::PhantomData<K>,
}

impl<'a, K> Iterator for BitVecIter<'a, K>
where
    K: TryFrom<usize>,
{
    type Item = (K, &'a bool);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|i| (i.try_into().ok().unwrap(), &true))
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.iter
            .nth(n)
            .map(|i| (i.try_into().ok().unwrap(), &true))
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

impl<'a, K> DoubleEndedIterator for BitVecIter<'a, K>
where
    K: TryFrom<usize>,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()
            .map(|i| (i.try_into().ok().unwrap(), &true))
    }
}

impl<'a, K> FusedIterator for BitVecIter<'a, K> where K: TryFrom<usize> {}

// TODO: Implementations for HashSet, BTreeSet, HashMap, BTreeMap.
