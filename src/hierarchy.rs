use std::iter::FusedIterator;
use std::mem::{replace, take};
use thiserror::Error;

use crate::secondary::SecondaryMap;
use crate::NodeIndex;

/// Hierarchical structure on top of a [`PortGraph`].
///
/// The order of child nodes is maintained as a doubly linked list which
/// supports efficient insertion and removal at any point in the list.
///
/// [`PortGraph`]: crate::portgraph::PortGraph
#[derive(Debug, Clone)]
pub struct Hierarchy {
    data: SecondaryMap<NodeIndex, NodeData>,
}

impl Hierarchy {
    /// Creates a new empty layout.
    pub fn new() -> Self {
        Self {
            data: SecondaryMap::new(),
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
    pub fn attach_last(&mut self, node: NodeIndex, parent: NodeIndex) -> Result<(), AttachError> {
        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle);
        } else if self.get(node).parent.is_some() {
            return Err(AttachError::AlreadyAttached);
        }

        let parent_data = self.get_mut(parent);
        parent_data.children_count += 1;
        let node_prev = replace(&mut self.get_mut(parent).children[1], Some(node));

        let node_data = self.get_mut(node);
        node_data.parent = Some(parent);
        node_data.siblings[0] = node_prev;

        match node_prev {
            Some(prev) => self.get_mut(prev).siblings[1] = Some(node),
            None => self.get_mut(parent).children[0] = Some(node),
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
    pub fn attach_first(&mut self, node: NodeIndex, parent: NodeIndex) -> Result<(), AttachError> {
        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle);
        } else if self.get(node).parent.is_some() {
            return Err(AttachError::AlreadyAttached);
        }

        let parent_data = self.get_mut(parent);
        parent_data.children_count += 1;
        let node_next = replace(&mut self.get_mut(parent).children[0], Some(node));

        let node_data = self.get_mut(node);
        node_data.parent = Some(parent);
        node_data.siblings[1] = node_next;

        match node_next {
            Some(next) => self.get_mut(next).siblings[0] = Some(node),
            None => self.get_mut(parent).children[1] = Some(node),
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
    pub fn attach_before(&mut self, node: NodeIndex, before: NodeIndex) -> Result<(), AttachError> {
        if self.get(node).parent.is_some() {
            return Err(AttachError::AlreadyAttached);
        }

        let Some(parent) = self.get(before).parent else {
            return Err(AttachError::RelativeToRoot);
        };

        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle);
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
            None => self.get_mut(parent).children[0] = Some(node),
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
    pub fn attach_after(&mut self, node: NodeIndex, after: NodeIndex) -> Result<(), AttachError> {
        if self.get(node).parent.is_some() {
            return Err(AttachError::AlreadyAttached);
        }

        let Some(parent) = self.get(after).parent else {
            return Err(AttachError::RelativeToRoot);
        };

        if !self.cycle_check(node, parent) {
            return Err(AttachError::Cycle);
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
            None => self.get_mut(parent).children[1] = Some(node),
        }

        Ok(())
    }

    /// Ensures that making `node` a child of `parent` would not introduce a cycle.
    fn cycle_check(&self, node: NodeIndex, mut parent: NodeIndex) -> bool {
        // When `node` does not have any children it can't contain `parent`.
        if self.get(node).children[0].is_none() {
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

            match siblings[0] {
                Some(prev) => self.get_mut(prev).siblings[1] = siblings[1],
                None => self.get_mut(parent).children[0] = siblings[1],
            }

            match siblings[1] {
                Some(next) => self.get_mut(next).siblings[0] = siblings[0],
                None => self.get_mut(parent).children[1] = siblings[0],
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
        let mut child_next = node_data.children[0];

        while let Some(child) = child_next {
            let child_data = self.get_mut(child);
            child_data.parent = None;
            let siblings = take(&mut child_data.siblings);
            child_next = siblings[1];
        }
    }

    /// Returns a node's parent or `None` if it is a root.
    #[inline]
    pub fn parent(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.get(node).parent
    }

    /// Returns a node's first child, if any.
    #[inline]
    pub fn first(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.get(parent).children[0]
    }

    /// Returns a node's last child, if any.
    #[inline]
    pub fn last(&self, parent: NodeIndex) -> Option<NodeIndex> {
        self.get(parent).children[1]
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
            next: node_data.children[0],
            prev: node_data.children[1],
            len: node_data.children_count as usize,
        }
    }

    /// Returns the number of the node's children.
    #[inline]
    pub fn child_count(&self, node: NodeIndex) -> usize {
        self.get(node).children_count as usize
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
                None => self.get_mut(parent).children[0] = Some(new),
            }

            match node_data.siblings[1] {
                Some(next) => self.get_mut(next).siblings[0] = Some(new),
                None => self.get_mut(parent).children[1] = Some(new),
            }
        }

        let mut next_child = node_data.children[0];

        while let Some(child) = next_child {
            let child_data = self.get_mut(child);
            child_data.parent = Some(new);
            next_child = child_data.siblings[1];
        }

        *self.get_mut(new) = node_data;
    }

    /// Reserves enough capacity to fit a maximum node index without reallocating.
    /// Does nothing if there already is enough capacity.
    pub fn ensure_capacity(&mut self, capacity: usize) {
        self.data.ensure_capacity(capacity);
    }

    // TODO: API to shrink
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NodeData {
    /// The first and last child of the node, if any.
    children: [Option<NodeIndex>; 2],
    /// The number of children
    children_count: u32,
    /// The parent of a node, if any.
    parent: Option<NodeIndex>,
    /// The sibilings of a node, if any.
    siblings: [Option<NodeIndex>; 2],
}

impl NodeData {
    pub const fn new() -> Self {
        Self {
            children: [None; 2],
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
#[derive(Clone)]
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

#[derive(Debug, Clone, Error)]
pub enum AttachError {
    #[error("the node is already attached")]
    AlreadyAttached,
    #[error("can not attach relative to a root node")]
    RelativeToRoot,
    #[error("attaching the node would introduce a cycle")]
    Cycle,
}
