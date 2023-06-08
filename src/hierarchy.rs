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
//! # use portgraph::{PortGraph, NodeIndex, PortIndex};
//! # use portgraph::hierarchy::Hierarchy;
//! let mut graph = PortGraph::new();
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

use std::iter::FusedIterator;
use std::mem::{replace, take};
use thiserror::Error;

use crate::unmanaged::UnmanagedDenseMap;
use crate::NodeIndex;

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
    pub fn new() -> Self {
        Self {
            data: UnmanagedDenseMap::new(),
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
        node_data.parent = Some(parent);

        let parent_data = self.get_mut(parent);
        parent_data.children_count += 1;
        match &mut parent_data.children {
            Some([_, prev]) => {
                let prev = replace(prev, node);
                self.get_mut(node).siblings[0] = Some(prev);
                self.get_mut(prev).siblings[1] = Some(node);
            }
            None => {
                parent_data.children = Some([node, node]);
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
        node_data.parent = Some(parent);

        let parent_data = self.get_mut(parent);
        parent_data.children_count += 1;
        match &mut parent_data.children {
            Some([next, _]) => {
                let next = replace(next, node);
                self.get_mut(node).siblings[1] = Some(next);
                self.get_mut(next).siblings[0] = Some(node);
            }
            None => {
                parent_data.children = Some([node, node]);
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

        let Some(parent) = self.get(before).parent else {
            return Err(AttachError::RootSibling{root: before});
        };

        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle { node, parent });
        }

        self.get_mut(parent).children_count += 1;
        let before_prev = replace(&mut self.get_mut(before).siblings[0], Some(node));

        {
            let node_data = self.get_mut(node);
            node_data.parent = Some(parent);
            node_data.siblings = [before_prev, Some(before)];
        }

        match before_prev {
            Some(prev) => self.get_mut(prev).siblings[1] = Some(node),
            None => self.get_mut(parent).children.as_mut().unwrap()[0] = node,
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

        let Some(parent) = self.get(after).parent else {
            return Err(AttachError::RootSibling{root: after});
        };

        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle { node, parent });
        }

        self.get_mut(parent).children_count += 1;
        let after_next = replace(&mut self.get_mut(after).siblings[1], Some(node));

        {
            let node_data = self.get_mut(node);
            node_data.parent = Some(parent);
            node_data.siblings = [Some(after), after_next];
        }

        match after_next {
            Some(next) => self.get_mut(next).siblings[0] = Some(node),
            None => self.get_mut(parent).children.as_mut().unwrap()[1] = node,
        }

        Ok(())
    }

    /// Ensures that making `node` a child of `parent` would not introduce a cycle.
    fn cycle_check(&self, node: NodeIndex, mut parent: NodeIndex) -> bool {
        // When `node` does not have any children it can't contain `parent`.
        if self.get(node).children.is_none() {
            return true;
        }

        loop {
            if parent == node {
                return false;
            } else if let Some(next) = self.get(parent).parent {
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
        let parent = take(&mut node_data.parent);
        let siblings = take(&mut node_data.siblings);

        if let Some(parent) = parent {
            self.get_mut(parent).children_count -= 1;

            if let Some(prev) = siblings[0] {
                self.get_mut(prev).siblings[1] = siblings[1];
            }
            if let Some(next) = siblings[1] {
                self.get_mut(next).siblings[0] = siblings[0];
            }

            match siblings {
                [None, None] => self.get_mut(parent).children = None,
                [Some(prev), None] => self.get_mut(parent).children.as_mut().unwrap()[1] = prev,
                [None, Some(next)] => self.get_mut(parent).children.as_mut().unwrap()[0] = next,
                _ => {}
            }
        }

        parent
    }

    /// Detaches all children from a node.
    pub fn detach_children(&mut self, node: NodeIndex) {
        let Some(node_data) = self.try_get_mut(node) else {
            return;
        };

        node_data.children_count = 0;
        let mut child_next = node_data.children.map(|c| c[0]);
        node_data.children = None;

        while let Some(child) = child_next {
            let child_data = self.get_mut(child);
            child_data.parent = None;
            let siblings = take(&mut child_data.siblings);
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
        self.get(node).parent
    }

    /// Returns whether a node is a root.
    #[inline]
    pub fn is_root(&self, node: NodeIndex) -> bool {
        self.parent(node).is_none()
    }

    /// Returns a node's first child, if any.
    #[inline]
    pub fn first(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.get(parent).children.map(|c| c[0])
    }

    /// Returns a node's last child, if any.
    #[inline]
    pub fn last(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.get(parent).children.map(|c| c[1])
    }

    /// Returns the next sibling in the node's parent, if any.
    ///
    /// Also returns `None` if the node is a root.
    #[inline]
    pub fn next(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.get(node).siblings[1]
    }

    /// Returns the previous sibling in the node's parent, if any.
    ///
    /// Also returns `None` if the node is a root.
    #[inline]
    pub fn prev(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.get(node).siblings[0]
    }

    /// Iterates over the node's children.
    #[inline]
    pub fn children(&self, node: NodeIndex) -> Children<'_> {
        let node_data = &self.get(node);
        Children {
            layout: self,
            next: node_data.children.map(|c| c[0]),
            prev: node_data.children.map(|c| c[1]),
            len: node_data.children_count as usize,
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

    /// Changes the index of a node from `old` to `new`.
    ///
    /// # Panics
    ///
    /// Panics if the index `new` is not a root without any children.
    pub fn rekey(&mut self, old: NodeIndex, new: NodeIndex) {
        if self.get(new) != &NodeData::default() {
            panic!("can not rekey into an occupied slot");
        }

        let node_data = take(self.get_mut(old));

        if let Some(parent) = node_data.parent {
            match node_data.siblings[0] {
                Some(prev) => self.get_mut(prev).siblings[1] = Some(new),
                None => self.get_mut(parent).children.as_mut().unwrap()[0] = new,
            }

            match node_data.siblings[1] {
                Some(next) => self.get_mut(next).siblings[0] = Some(new),
                None => self.get_mut(parent).children.as_mut().unwrap()[1] = new,
            }
        }

        let mut next_child = node_data.children.map(|c| c[0]);

        while let Some(child) = next_child {
            let child_data = self.get_mut(child);
            child_data.parent = Some(new);
            next_child = child_data.siblings[1];
        }

        *self.get_mut(new) = node_data;
        *self.get_mut(old) = NodeData::default();
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

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
struct NodeData {
    /// The first and last child of the node, if any.
    children: Option<[NodeIndex; 2]>,
    /// The number of children
    children_count: u32,
    /// The parent of a node, if any.
    parent: Option<NodeIndex>,
    /// The siblings of a node, if any.
    siblings: [Option<NodeIndex>; 2],
}

impl NodeData {
    pub const fn new() -> Self {
        Self {
            children: None,
            children_count: 0u32,
            parent: None,
            siblings: [None; 2],
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
    next: Option<NodeIndex>,
    prev: Option<NodeIndex>,
    len: usize,
}

impl<'a> Iterator for Children<'a> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let current = self.next.unwrap();
        self.next = self.layout.next(current);
        Some(current)
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a> DoubleEndedIterator for Children<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        let current = self.prev.unwrap();
        self.prev = self.layout.prev(current);
        Some(current)
    }
}

impl<'a> ExactSizeIterator for Children<'a> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a> FusedIterator for Children<'a> {}

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
    use crate::PortGraph;

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
        assert_eq!(hierarchy.parent(root), None);
        assert_eq!(hierarchy.first(root), Some(child0));
        assert_eq!(hierarchy.last(root), Some(child2));
        assert_eq!(hierarchy.next(root), None);
        assert_eq!(hierarchy.prev(root), None);

        for child in children {
            assert_eq!(hierarchy.parent(child), Some(root));
            assert_eq!(hierarchy.child_count(child), 0);
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
    fn test_graph_compact() {
        let mut graph = PortGraph::new();
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
