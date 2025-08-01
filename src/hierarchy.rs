//! Hierarchical structure on top of a [`PortGraph`]. This is a separate
//! relation from the graph's adjacency.
//!
//! The nodes form a forest, with each node having at most a single parent, and
//! any number of children. Cycles are not allowed.
//!
//! This map does not allocate any memory until a value is modified. It is
//! intended to be used alongside [`PortGraph`], as it does not keep track of
//! key validity.
//!
//! [`PortGraph`]: crate::portgraph::PortGraph
//!
//! # Example
//!
//! ```
//! # use ::portgraph::*;
//! let mut graph: PortGraph = PortGraph::new();
//! let mut hierarchy = Hierarchy::new();
//!
//! let parent = graph.add_node(0, 0);
//! assert!(hierarchy.is_root(parent));
//! assert_eq!(hierarchy.child_count(parent), 0);
//!
//! // Add some children.
//! let child_0 = graph.add_node(0, 0);
//! let child_1 = graph.add_node(0, 0);
//! hierarchy.push_child(child_1, parent).unwrap();
//! hierarchy.insert_before(child_0, child_1).unwrap();
//!
//! assert_eq!(hierarchy.child_count(parent), 2);
//! assert_eq!(hierarchy.children(parent).collect::<Vec<_>>(), vec![child_0, child_1]);
//!
//! assert_eq!(hierarchy.parent(child_0), Some(parent));
//! assert_eq!(hierarchy.prev(child_0), None);
//! assert_eq!(hierarchy.next(child_0), Some(child_1));
//!
//! // Modifications to the graph must be manually propagated to the hierarchy.
//! graph.remove_node(parent);
//! hierarchy.remove(parent);
//!
//! assert!(hierarchy.is_root(child_0));
//! assert!(hierarchy.is_root(child_1));
//! assert_eq!(hierarchy.next(child_0), None);
//!
//! graph.compact_nodes(|old, new| {
//!     hierarchy.rekey(old, new);
//! });
//! hierarchy.shrink_to(graph.node_count());
//! ```

use std::borrow::Cow;
use std::collections::VecDeque;
use std::iter::FusedIterator;
use std::mem;
use thiserror::Error;

use crate::index::MaybeNodeIndex;
use crate::unmanaged::UnmanagedDenseMap;
use crate::{NodeIndex, SecondaryMap};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Hierarchical structure on top of a [`PortGraph`].
///
/// The order of child nodes is maintained as a doubly linked list which
/// supports efficient insertion and removal at any point in the list.
///
/// [`PortGraph`]: crate::portgraph::PortGraph
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct Hierarchy {
    data: UnmanagedDenseMap<NodeIndex, NodeData>,
}

impl Hierarchy {
    /// Creates a new empty layout.
    pub const fn new() -> Self {
        Self {
            data: UnmanagedDenseMap::with_default(NodeData::new()),
        }
    }

    /// Creates a new empty layout with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: UnmanagedDenseMap::with_capacity(capacity),
        }
    }
}

impl Default for Hierarchy {
    fn default() -> Self {
        Self::new()
    }
}

impl Hierarchy {
    #[inline]
    fn get_mut(&mut self, node: NodeIndex) -> &mut NodeData {
        self.data.get_mut(node)
    }

    #[inline]
    fn try_get_mut(&mut self, node: NodeIndex) -> Option<&mut NodeData> {
        self.data.try_get_mut(node)
    }

    #[inline]
    fn get(&self, node: NodeIndex) -> &NodeData {
        self.data.get(node)
    }

    /// Attaches a node as the last child of a parent node.
    ///
    /// # Errors
    ///
    ///  - When the attachment would introduce a cycle.
    ///  - When the node is already attached.
    ///
    /// # Panics
    ///
    /// Panics when the parent node will have more than `u32::MAX` children.
    pub fn push_child(&mut self, node: NodeIndex, parent: NodeIndex) -> Result<(), AttachError> {
        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle { node, parent });
        } else if self.get(node).parent.is_some() {
            return Err(AttachError::AlreadyAttached { node });
        }

        let node_data = self.get_mut(node);
        node_data.parent = parent.into();

        let parent_data = self.get_mut(parent);
        parent_data.children_count += 1;
        match &mut parent_data.children {
            [_, prev] if prev.is_some() => {
                let prev = prev.replace(node);
                self.get_mut(node).siblings[0] = prev;
                self.get_mut(prev.unwrap()).siblings[1] = node.into();
            }
            _ => {
                let node = MaybeNodeIndex::from(node);
                parent_data.children = [node, node];
            }
        }

        Ok(())
    }

    /// Attaches a node as the first child of a parent node.
    ///
    /// # Errors
    ///
    ///  - When the attachment would introduce a cycle.
    ///  - When the node is already attached.
    ///
    /// # Panics
    ///
    /// Panics when the parent node will have more than `u32::MAX` children.
    pub fn push_front_child(
        &mut self,
        node: NodeIndex,
        parent: NodeIndex,
    ) -> Result<(), AttachError> {
        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle { node, parent });
        } else if self.get(node).parent.is_some() {
            return Err(AttachError::AlreadyAttached { node });
        }

        let node_data = self.get_mut(node);
        node_data.parent = parent.into();

        let parent_data = self.get_mut(parent);
        parent_data.children_count += 1;
        match &mut parent_data.children {
            [next, _] if next.is_some() => {
                let next = next.replace(node);
                self.get_mut(node).siblings[1] = next;
                self.get_mut(next.unwrap()).siblings[0] = node.into();
            }
            _ => {
                let node = MaybeNodeIndex::from(node);
                parent_data.children = [node, node];
            }
        }

        Ok(())
    }

    /// Attaches a node before another node within the other node's parent.
    ///
    /// # Errors
    ///
    ///  - When the attachment would introduce a cycle.
    ///  - When the node is already attached.
    ///  - When the other node is a root.
    ///
    /// # Panics
    ///
    /// Panics when the parent node will have more than `u32::MAX` children.
    pub fn insert_before(&mut self, node: NodeIndex, before: NodeIndex) -> Result<(), AttachError> {
        if self.get(node).parent.is_some() {
            return Err(AttachError::AlreadyAttached { node });
        }

        let Some(parent) = self.get(before).parent.to_option() else {
            return Err(AttachError::RootSibling { root: before });
        };

        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle { node, parent });
        }

        self.get_mut(parent).children_count += 1;
        let before_prev = self.get_mut(before).siblings[0].replace(node);

        {
            let node_data = self.get_mut(node);
            node_data.parent = parent.into();
            node_data.siblings = [before_prev, before.into()];
        }

        match before_prev.to_option() {
            Some(prev) => self.get_mut(prev).siblings[1] = node.into(),
            None => self.get_mut(parent).children[0] = node.into(),
        }

        Ok(())
    }

    /// Attaches a node after another node within the other node's parent.
    ///
    /// # Errors
    ///
    ///  - When the attachment would introduce a cycle.
    ///  - When the node is already attached.
    ///  - When the other node is a root.
    ///
    /// # Panics
    ///
    /// Panics when the parent node will have more than `u32::MAX` children.
    pub fn insert_after(&mut self, node: NodeIndex, after: NodeIndex) -> Result<(), AttachError> {
        if self.get(node).parent.is_some() {
            return Err(AttachError::AlreadyAttached { node });
        }

        let Some(parent) = self.get(after).parent.to_option() else {
            return Err(AttachError::RootSibling { root: after });
        };

        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle { node, parent });
        }

        self.get_mut(parent).children_count += 1;
        let after_next = self.get_mut(after).siblings[1].replace(node);

        {
            let node_data = self.get_mut(node);
            node_data.parent = parent.into();
            node_data.siblings = [after.into(), after_next];
        }

        match after_next.to_option() {
            Some(next) => self.get_mut(next).siblings[0] = node.into(),
            None => self.get_mut(parent).children[1] = node.into(),
        }

        Ok(())
    }

    /// Ensures that making `node` a child of `parent` would not introduce a cycle.
    fn cycle_check(&self, node: NodeIndex, mut parent: NodeIndex) -> bool {
        // When `node` does not have any children it can't contain `parent`.
        if self.get(node).children[0].is_none() {
            debug_assert!(self.get(node).children[1].is_none());
            return true;
        }

        loop {
            if parent == node {
                return false;
            } else if let Some(next) = self.get(parent).parent.to_option() {
                parent = next;
            } else {
                return true;
            }
        }
    }

    /// Detaches a node from its parent, returning the former parent.
    ///
    /// Does nothing and returns `None` when the node is a root.
    pub fn detach(&mut self, node: NodeIndex) -> Option<NodeIndex> {
        let node_data = self.try_get_mut(node)?;
        let parent = node_data.parent.take();
        let siblings = mem::take(&mut node_data.siblings);

        if let Some(parent) = parent.to_option() {
            self.get_mut(parent).children_count -= 1;

            if let Some(prev) = siblings[0].to_option() {
                self.get_mut(prev).siblings[1] = siblings[1];
            }
            if let Some(next) = siblings[1].to_option() {
                self.get_mut(next).siblings[0] = siblings[0];
            }

            match siblings.map(|s| s.to_option()) {
                [None, None] => self.get_mut(parent).children = siblings,
                [Some(_), None] => self.get_mut(parent).children[1] = siblings[0],
                [None, Some(_)] => self.get_mut(parent).children[0] = siblings[1],
                _ => {}
            }
        }

        parent.to_option()
    }

    /// Detaches all children from a node.
    pub fn detach_children(&mut self, node: NodeIndex) {
        let Some(node_data) = self.try_get_mut(node) else {
            return;
        };

        node_data.children_count = 0;
        let mut child_next = node_data.children[0];
        node_data.children = [None.into(), None.into()];

        while let Some(child) = child_next.to_option() {
            let child_data = self.get_mut(child);
            child_data.parent = None.into();
            let siblings = mem::take(&mut child_data.siblings);
            child_next = siblings[1];
        }
    }

    /// Removes a node from the hierarchy, detaching it from its parent and
    /// detaching all its children.
    pub fn remove(&mut self, node: NodeIndex) {
        self.detach_children(node);
        self.detach(node);
    }

    /// Returns a node's parent or `None` if it is a root.
    #[inline]
    pub fn parent(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.get(node).parent.to_option()
    }

    /// Returns whether a node is a root.
    #[inline]
    pub fn is_root(&self, node: NodeIndex) -> bool {
        self.parent(node).is_none()
    }

    /// Returns a node's first child, if any.
    #[inline]
    pub fn first(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.get(parent).children[0].to_option()
    }

    /// Returns a node's last child, if any.
    #[inline]
    pub fn last(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.get(parent).children[1].to_option()
    }

    /// Returns the next sibling in the node's parent, if any.
    ///
    /// Also returns `None` if the node is a root.
    #[inline]
    pub fn next(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.get(node).siblings[1].to_option()
    }

    /// Returns the previous sibling in the node's parent, if any.
    ///
    /// Also returns `None` if the node is a root.
    #[inline]
    pub fn prev(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.get(node).siblings[0].to_option()
    }

    /// Iterates over the node's children.
    #[inline]
    pub fn children(&self, node: NodeIndex) -> Children<'_> {
        let node_data = self.get(node);
        let [next, prev] = node_data.children;
        Children {
            layout: self,
            next,
            prev,
            len: node_data.children_count as usize,
        }
    }

    /// Iterates over the node's descendants.
    ///
    /// Traverses the hierarchy in breadth-first order.
    ///
    /// The iterator will yield the node itself first, followed by its children.
    pub fn descendants(&self, node: NodeIndex) -> Descendants<'_> {
        Descendants {
            layout: self,
            node_queue: NextStates::Root(node),
        }
    }

    /// Returns the number of the node's children.
    #[inline]
    pub fn child_count(&self, node: NodeIndex) -> usize {
        self.get(node).children_count as usize
    }

    /// Returns whether a node has any children.
    #[inline]
    pub fn has_children(&self, node: NodeIndex) -> bool {
        self.child_count(node) > 0
    }

    /// Swap the positions of two nodes.
    pub fn swap_nodes(&mut self, a: NodeIndex, b: NodeIndex) {
        if a == b {
            return;
        }

        // Get a copy of the data. We leave the original data in place for the
        // moment in case one of the nodes is the parent of the other.
        let mut a_data = *self.get(a);
        let mut b_data = *self.get(b);

        self.rekey_in_children(a_data, b);
        self.rekey_in_children(b_data, a);

        self.rekey_in_parent(a_data, b);
        self.rekey_in_parent(b_data, a);

        self.rekey_in_siblings(a_data, b);
        self.rekey_in_siblings(b_data, a);

        // Update the nodes' data, if they are siblings or one is the parent of
        // the other.
        let rekey_in_value =
            |val: Option<&mut NodeIndex>, old_other: NodeIndex, new_other: NodeIndex| match val {
                Some(val) if *val == old_other => *val = new_other,
                _ => (),
            };
        let rekey_in_data = |data: &mut NodeData, old: NodeIndex, new: NodeIndex| {
            rekey_in_value(data.parent.as_mut(), old, new);
            rekey_in_value(data.children[0].as_mut(), old, new);
            rekey_in_value(data.children[1].as_mut(), old, new);
            rekey_in_value(data.siblings[0].as_mut(), old, new);
            rekey_in_value(data.siblings[1].as_mut(), old, new);
        };
        rekey_in_data(&mut a_data, b, a);
        rekey_in_data(&mut b_data, a, b);

        self.data.set(a, b_data);
        self.data.set(b, a_data);
    }

    /// Changes the index of a node from `old` to `new`.
    ///
    /// # Panics
    ///
    /// Panics if the index `new` is not a root without any children.
    pub fn rekey(&mut self, old: NodeIndex, new: NodeIndex) {
        if self.get(new) != &NodeData::default() {
            panic!("can not rekey into an occupied slot");
        }
        if old == new {
            return;
        }
        let node_data = mem::take(self.get_mut(old));

        self.rekey_in_children(node_data, new);
        self.rekey_in_parent(node_data, new);
        self.rekey_in_siblings(node_data, new);

        self.data.set(new, node_data);
    }

    /// Update a node's key in its parent's children list.
    #[inline]
    fn rekey_in_parent(&mut self, data: NodeData, new_node: NodeIndex) {
        if let Some(parent) = data.parent.to_option() {
            if data.siblings[0].is_none() {
                self.get_mut(parent).children.as_mut()[0] = new_node.into();
            }
            if data.siblings[1].is_none() {
                self.get_mut(parent).children.as_mut()[1] = new_node.into();
            }
        }
    }

    /// Update a node's key in its immediate siblings data.
    #[inline]
    fn rekey_in_siblings(&mut self, data: NodeData, new: NodeIndex) {
        if let Some(prev) = data.siblings[0].to_option() {
            self.get_mut(prev).siblings[1] = new.into();
        }
        if let Some(next) = data.siblings[1].to_option() {
            self.get_mut(next).siblings[0] = new.into();
        }
    }

    /// Update a node's key in it's children data.
    #[inline]
    fn rekey_in_children(&mut self, data: NodeData, new: NodeIndex) {
        let mut next_child = data.children[0];
        while let Some(child) = next_child.to_option() {
            let child_data = self.get_mut(child);
            child_data.parent = new.into();
            next_child = child_data.siblings[1];
        }
    }

    /// Reserves enough capacity to fit a maximum node index without reallocating.
    /// Does nothing if there already is enough capacity.
    pub fn ensure_capacity(&mut self, capacity: usize) {
        self.data.ensure_capacity(capacity);
    }

    /// Reduces the capacity of the structure to `capacity`.
    /// Nodes with index higher than `capacity` are disconnected.
    ///
    /// Does nothing when the capacity of the secondary map is already lower.
    pub fn shrink_to(&mut self, capacity: usize) {
        for node in (capacity..self.data.capacity()).rev() {
            self.remove(NodeIndex::new(node));
        }
        self.data.shrink_to(capacity);
    }
}

impl<'a> From<&'a Hierarchy> for Cow<'a, Hierarchy> {
    fn from(hierarchy: &'a Hierarchy) -> Self {
        Cow::Borrowed(hierarchy)
    }
}

impl From<Hierarchy> for Cow<'_, Hierarchy> {
    fn from(hierarchy: Hierarchy) -> Self {
        Cow::Owned(hierarchy)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
struct NodeData {
    /// The first and last child of the node, if any.
    ///
    /// Either both have a value or none of them do.
    children: [MaybeNodeIndex<u32>; 2],
    /// The number of children
    children_count: u32,
    /// The parent of a node, if any.
    parent: MaybeNodeIndex<u32>,
    /// The siblings of a node, if any.
    siblings: [MaybeNodeIndex<u32>; 2],
}

impl NodeData {
    pub const fn new() -> Self {
        Self {
            children: [MaybeNodeIndex::NONE; 2],
            children_count: 0u32,
            parent: MaybeNodeIndex::NONE,
            siblings: [MaybeNodeIndex::NONE; 2],
        }
    }
}

impl Default for NodeData {
    fn default() -> Self {
        Self::new()
    }
}

/// Iterator created by [`Hierarchy::children`].
#[derive(Clone, Debug)]
pub struct Children<'a> {
    layout: &'a Hierarchy,
    next: MaybeNodeIndex<u32>,
    prev: MaybeNodeIndex<u32>,
    len: usize,
}

impl Default for Children<'static> {
    fn default() -> Self {
        static HIERARCHY: Hierarchy = Hierarchy::new();
        Self {
            layout: &HIERARCHY,
            next: MaybeNodeIndex::NONE,
            prev: MaybeNodeIndex::NONE,
            len: 0,
        }
    }
}

impl Iterator for Children<'_> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let current = self.next.unwrap();
        self.next = self.layout.next(current).into();
        Some(current)
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl DoubleEndedIterator for Children<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let current = self.prev.unwrap();
        self.prev = self.layout.prev(current).into();
        Some(current)
    }
}

impl ExactSizeIterator for Children<'_> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.len
    }
}

impl FusedIterator for Children<'_> {}

/// Iterator created by [`Hierarchy::descendants`].
///
/// Traverses the descendants of a node in breadth-first order.
#[derive(Clone, Debug)]
pub struct Descendants<'a> {
    /// The hierarchy this iterator is iterating over.
    layout: &'a Hierarchy,
    /// A queue of regions to visit.
    ///
    /// For each region, we point to a child node that has not been visited yet.
    /// When a region is visited, we move to the next child node and queue its children region at the end of the queue.
    node_queue: NextStates,
}

/// A queue of nodes to visit next in the [`Descendants`] iterator.
#[derive(Clone, Debug)]
enum NextStates {
    /// The iterator hasn't been queried yet. It stores only the root node.
    Root(NodeIndex),
    /// We are in the process of exploring the descendants.
    /// This queue does **not** include the root node.
    Descendants(VecDeque<NodeIndex>),
}

impl NextStates {
    /// Returns the number of nodes currently in the queue.
    fn len(&self) -> usize {
        match self {
            Self::Root(_) => 1,
            Self::Descendants(queue) => queue.len(),
        }
    }
}

impl Default for Descendants<'static> {
    fn default() -> Self {
        static HIERARCHY: Hierarchy = Hierarchy::new();
        Self {
            layout: &HIERARCHY,
            node_queue: NextStates::Descendants(VecDeque::new()),
        }
    }
}

impl Iterator for Descendants<'_> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        if let NextStates::Root(root) = &self.node_queue {
            let root = *root;
            self.node_queue = NextStates::Descendants(VecDeque::from_iter(self.layout.first(root)));
            return Some(root);
        };
        let NextStates::Descendants(queue) = &mut self.node_queue else {
            unreachable!()
        };

        // The next element is always the first node in the queue.
        let next = queue.pop_front()?;

        // Check if the node had a next sibling and add it to the front of
        // queue.
        if let Some(next_sibling) = self.layout.next(next) {
            queue.push_front(next_sibling);
        }

        // Now add the children region of `next` to the end of the queue.
        if let Some(child) = self.layout.first(next) {
            queue.push_back(child);
        }

        Some(next)
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.node_queue.len(), None)
    }
}

impl FusedIterator for Descendants<'_> {}

/// Error produced when trying to attach nodes in the Hierarchy.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum AttachError {
    /// The node is already attached to a parent.
    #[error("the node {node:?} is already attached")]
    AlreadyAttached { node: NodeIndex },
    /// The target node is a root node, and cannot have siblings.
    #[error("can not attach a sibling to root node {root:?}")]
    RootSibling { root: NodeIndex },
    /// The relation would introduce a cycle.
    #[error("attaching the node {node:?} to {parent:?} would introduce a cycle")]
    Cycle { node: NodeIndex, parent: NodeIndex },
}

#[cfg(test)]
mod test {
    use itertools::Itertools;

    use crate::{PortGraph, PortMut, PortView};

    use super::*;

    #[test]
    fn test_basic() {
        let mut hierarchy = Hierarchy::new();
        let root = NodeIndex::new(4);

        assert_eq!(hierarchy.child_count(root), 0);
        assert_eq!(hierarchy.parent(root), None);
        assert_eq!(hierarchy.first(root), None);
        assert_eq!(hierarchy.last(root), None);
        assert_eq!(hierarchy.next(root), None);
        assert_eq!(hierarchy.prev(root), None);

        // root
        //  |-> child0
        //  |-> child1
        //   -> child2
        let child0 = NodeIndex::new(0);
        let child1 = NodeIndex::new(1);
        let child2 = NodeIndex::new(2);
        let children = [child0, child1, child2];
        hierarchy.push_front_child(child0, root).unwrap();
        hierarchy.push_child(child2, root).unwrap();
        hierarchy.insert_after(child1, child0).unwrap();

        assert_eq!(
            hierarchy.push_front_child(root, child2),
            Err(AttachError::Cycle {
                node: root,
                parent: child2
            })
        );
        assert_eq!(
            hierarchy.push_front_child(child2, root),
            Err(AttachError::AlreadyAttached { node: child2 })
        );

        assert_eq!(hierarchy.child_count(root), 3);
        assert_eq!(
            hierarchy.children(root).collect::<Vec<_>>(),
            vec![child0, child1, child2]
        );
        assert_eq!(
            hierarchy.descendants(root).collect::<Vec<_>>(),
            vec![root, child0, child1, child2]
        );
        assert_eq!(hierarchy.parent(root), None);
        assert_eq!(hierarchy.first(root), Some(child0));
        assert_eq!(hierarchy.last(root), Some(child2));
        assert_eq!(hierarchy.next(root), None);
        assert_eq!(hierarchy.prev(root), None);

        for child in children {
            assert_eq!(hierarchy.parent(child), Some(root));
            assert_eq!(hierarchy.child_count(child), 0);
            // https://github.com/CQCL/portgraph/issues/177
            assert_eq!(hierarchy.descendants(child).collect_vec(), vec![child]);
        }
        assert_eq!(hierarchy.prev(child0), None);
        assert_eq!(hierarchy.next(child0), Some(child1));
        assert_eq!(hierarchy.prev(child1), Some(child0));
        assert_eq!(hierarchy.next(child1), Some(child2));
        assert_eq!(hierarchy.prev(child2), Some(child1));
        assert_eq!(hierarchy.next(child2), None);
    }

    #[test]
    fn test_detach() {
        let mut hierarchy = Hierarchy::new();
        let root = NodeIndex::new(4);

        let child0 = NodeIndex::new(0);
        let child1 = NodeIndex::new(1);
        let child2 = NodeIndex::new(2);
        hierarchy.push_child(child2, root).unwrap();
        hierarchy.insert_before(child1, child2).unwrap();
        hierarchy.insert_before(child0, child1).unwrap();

        assert_eq!(
            hierarchy.children(root).collect::<Vec<_>>(),
            vec![child0, child1, child2]
        );

        hierarchy.detach(child1).unwrap();

        assert_eq!(
            hierarchy.children(root).collect::<Vec<_>>(),
            vec![child0, child2]
        );

        assert_eq!(hierarchy.prev(child0), None);
        assert_eq!(hierarchy.next(child0), Some(child2));
        assert_eq!(hierarchy.prev(child2), Some(child0));
        assert_eq!(hierarchy.next(child2), None);

        assert_eq!(hierarchy.parent(child1), None);
        assert_eq!(hierarchy.prev(child1), None);
        assert_eq!(hierarchy.next(child1), None);

        hierarchy.detach_children(root);

        assert_eq!(hierarchy.first(root), None);
        assert_eq!(hierarchy.last(root), None);
        assert_eq!(hierarchy.children(root).collect::<Vec<_>>(), vec![]);
        for child in [child0, child2] {
            assert_eq!(hierarchy.parent(child), None);
            assert_eq!(hierarchy.prev(child), None);
            assert_eq!(hierarchy.next(child), None);
        }
    }

    #[test]
    fn test_rekey() {
        let mut hierarchy = Hierarchy::new();
        let root = NodeIndex::new(4);

        let child0 = NodeIndex::new(0);
        let child1 = NodeIndex::new(1);
        let child2 = NodeIndex::new(2);
        hierarchy.push_child(child2, root).unwrap();
        hierarchy.insert_before(child1, child2).unwrap();
        hierarchy.insert_before(child0, child1).unwrap();

        assert_eq!(
            hierarchy.children(root).collect::<Vec<_>>(),
            vec![child0, child1, child2]
        );

        let grandchild = NodeIndex::new(42);
        hierarchy.push_front_child(grandchild, child1).unwrap();

        assert_eq!(
            hierarchy.children(root).collect::<Vec<_>>(),
            vec![child0, child1, child2]
        );
        assert_eq!(
            hierarchy.children(child1).collect::<Vec<_>>(),
            vec![grandchild]
        );

        let new_child1 = NodeIndex::new(8);
        hierarchy.rekey(child1, new_child1);

        assert_eq!(
            hierarchy.children(root).collect::<Vec<_>>(),
            vec![child0, new_child1, child2]
        );
        assert_eq!(
            hierarchy.children(new_child1).collect::<Vec<_>>(),
            vec![grandchild]
        );
        assert_eq!(hierarchy.parent(new_child1), Some(root));
        assert_eq!(hierarchy.parent(grandchild), Some(new_child1));

        assert_eq!(hierarchy.next(child0), Some(new_child1));
        assert_eq!(hierarchy.next(new_child1), Some(child2));
        assert_eq!(hierarchy.prev(new_child1), Some(child0));
        assert_eq!(hierarchy.prev(child2), Some(new_child1));

        hierarchy.remove(new_child1);
        assert_eq!(
            hierarchy.children(root).collect::<Vec<_>>(),
            vec![child0, child2]
        );
        assert!(hierarchy.is_root(grandchild));
    }

    #[test]
    fn test_swap() {
        let mut hierarchy = Hierarchy::new();
        let root = NodeIndex::new(4);

        let child0 = NodeIndex::new(0);
        let child1 = NodeIndex::new(1);
        let child2 = NodeIndex::new(2);
        hierarchy.push_child(child2, root).unwrap();
        hierarchy.insert_before(child1, child2).unwrap();
        hierarchy.insert_before(child0, child1).unwrap();

        let grandchild1 = NodeIndex::new(42);
        let grandchild2 = NodeIndex::new(8);
        hierarchy.push_child(grandchild1, child1).unwrap();
        hierarchy.push_child(grandchild2, child1).unwrap();

        // Swap unrelated nodes
        hierarchy.swap_nodes(child2, grandchild2);
        let (child2, grandchild2) = (grandchild2, child2);

        assert!(hierarchy.children(root).eq([child0, child1, child2]));
        assert!(hierarchy.children(child2).eq([]));
        assert!(hierarchy.children(child1).eq([grandchild1, grandchild2]));
        assert_eq!(hierarchy.parent(child2), Some(root));
        assert_eq!(hierarchy.parent(grandchild2), Some(child1));
        assert_eq!(hierarchy.prev(grandchild2), Some(grandchild1));
        assert_eq!(hierarchy.next(grandchild2), None);
        assert_eq!(hierarchy.next(grandchild1), Some(grandchild2));

        // Swap parent and child
        hierarchy.swap_nodes(root, child1);
        let (root, child1) = (child1, root);

        assert!(hierarchy.children(root).eq([child0, child1, child2]));
        assert!(hierarchy.children(child1).eq([grandchild1, grandchild2]));
        assert_eq!(hierarchy.parent(child1), Some(root));
        assert_eq!(hierarchy.parent(grandchild1), Some(child1));
        assert_eq!(hierarchy.parent(grandchild2), Some(child1));

        // Swap siblings
        hierarchy.swap_nodes(child1, child2);
        let (child1, child2) = (child2, child1);

        assert!(hierarchy.children(root).eq([child0, child1, child2]));
        assert!(hierarchy.children(child1).eq([grandchild1, grandchild2]));
        assert!(hierarchy.children(child2).eq([]));
        assert_eq!(hierarchy.next(child0), Some(child1));
        assert_eq!(hierarchy.next(child1), Some(child2));
        assert_eq!(hierarchy.next(child2), None);
        assert_eq!(hierarchy.prev(child0), None);
        assert_eq!(hierarchy.prev(child1), Some(child0));
        assert_eq!(hierarchy.prev(child2), Some(child1));
        assert_eq!(hierarchy.parent(child1), Some(root));
        assert_eq!(hierarchy.parent(grandchild1), Some(child1));
        assert_eq!(hierarchy.parent(grandchild2), Some(child1));
    }

    #[test]
    fn test_graph_compact() {
        let mut graph: PortGraph = PortGraph::new();
        let mut hierarchy = Hierarchy::new();

        let parent = graph.add_node(0, 0);
        let mut child_0 = graph.add_node(0, 0);
        let mut child_1 = graph.add_node(0, 0);
        hierarchy.push_front_child(child_1, parent).unwrap();
        hierarchy.insert_before(child_0, child_1).unwrap();

        // Modifications to the graph must be manually propagated to the hierarchy.
        graph.remove_node(parent);
        hierarchy.remove(parent);

        assert!(hierarchy.is_root(child_0));
        assert!(hierarchy.is_root(child_1));
        assert_eq!(hierarchy.next(child_0), None);

        hierarchy.push_front_child(child_1, child_0).unwrap();

        graph.compact_nodes(|old, new| {
            hierarchy.rekey(old, new);
            if old == child_0 {
                child_0 = new;
            } else if old == child_1 {
                child_1 = new;
            }
        });

        hierarchy.shrink_to(graph.node_count());

        assert!(hierarchy.is_root(child_0));
        assert_eq!(hierarchy.first(child_0), Some(child_1));
        assert_eq!(hierarchy.parent(child_1), Some(child_0));
    }

    #[cfg(feature = "serde")]
    #[test]
    fn hierarchy_serialize() {
        let mut hierarchy = Hierarchy::new();
        assert_eq!(crate::portgraph::test::ser_roundtrip(&hierarchy), hierarchy);
        let root = NodeIndex::new(4);

        let child0 = NodeIndex::new(0);
        let child1 = NodeIndex::new(1);
        let child2 = NodeIndex::new(2);
        hierarchy.push_front_child(child0, root).unwrap();
        hierarchy.push_child(child2, root).unwrap();
        hierarchy.insert_after(child1, child0).unwrap();

        assert_eq!(crate::portgraph::test::ser_roundtrip(&hierarchy), hierarchy);
    }
}
