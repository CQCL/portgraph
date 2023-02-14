use crate::{NodeIndex, PortIndex};

#[derive(Debug, Clone)]
pub struct Weights<N, P> {
    nodes: Vec<NodeWeight<N>>,
    ports: Vec<PortWeight<P>>,
}

#[derive(Default, Debug, Clone)]
struct NodeWeight<N>(Option<N>);

#[derive(Default, Debug, Clone)]
struct PortWeight<P>(Option<P>);

/// Trait for graphs that encode edges connecting nodes.
///
/// TODO: Do a proper API design for this, and fill in the todo!s.
impl<N, P> Weights<N, P> {
    /// Create a new weights component with no nodes or ports.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new weights component pre-allocating space for the given number of nodes and ports.
    pub fn with_capacity(nodes: usize, ports: usize) -> Self {
        Self {
            nodes: Vec::with_capacity(nodes),
            ports: Vec::with_capacity(ports),
        }
    }

    /// A mutable reference to the weight of the node with a given index.
    pub fn get_node_mut(&mut self, node: NodeIndex) -> &mut N
    where
        N: Default,
    {
        self.allocate_node(node);
        self.nodes[node.index()]
            .0
            .get_or_insert_with(Default::default)
    }

    /// A reference to the weight of the node with a given index.
    pub fn try_get_node_mut(&mut self, node: NodeIndex) -> Option<&mut N> {
        self.nodes.get_mut(node.index()).and_then(|p| p.0.as_mut())
    }

    /// A reference to the weight of the node with a given index.
    pub fn try_get_node(&self, node: NodeIndex) -> Option<&N> {
        self.nodes.get(node.index()).and_then(|n| n.0.as_ref())
    }

    /// Set the weight of the node with a given index.
    pub fn set_node(&mut self, node: NodeIndex, weight: N) {
        self.allocate_node(node);
        self.nodes[node.index()].0 = Some(weight);
    }

    /// Remove a node weight, returning it.
    pub fn remove_node(&mut self, node: NodeIndex) -> Option<N> {
        let mut weight = None;
        std::mem::swap(&mut self.nodes[node.index()].0, &mut weight);
        weight
    }

    /// Ensure that a node is allocated.
    fn allocate_node(&mut self, node: NodeIndex) {
        if node.index() >= self.nodes.len() {
            self.nodes
                .resize_with(node.index() + 1, || NodeWeight(None));
        }
    }

    /// A mutable reference to the weight of the port with a given index.
    pub fn get_port_mut(&mut self, port: PortIndex) -> &mut P
    where
        P: Default,
    {
        self.allocate_port(port);
        self.ports[port.index()]
            .0
            .get_or_insert_with(Default::default)
    }

    /// A reference to the weight of the port with a given index.
    pub fn try_get_port_mut(&mut self, p: PortIndex) -> Option<&mut P> {
        self.ports.get_mut(p.index()).and_then(|p| p.0.as_mut())
    }

    /// A reference to the weight of the port with a given index.
    pub fn try_get_port(&self, port: PortIndex) -> Option<&P> {
        self.ports.get(port.index()).and_then(|p| p.0.as_ref())
    }

    /// Set the weight of the node with a given index.
    pub fn set_port(&mut self, port: PortIndex, weight: P) {
        self.allocate_port(port);
        self.ports[port.index()].0 = Some(weight);
    }

    /// Remove a port weight, returning it.
    pub fn remove_port(&mut self, port: PortIndex) -> Option<P> {
        let mut weight = None;
        std::mem::swap(&mut self.ports[port.index()].0, &mut weight);
        weight
    }

    /// Ensure that a port is allocated.
    fn allocate_port(&mut self, port: PortIndex) {
        if port.index() >= self.ports.len() {
            self.ports
                .resize_with(port.index() + 1, || PortWeight(None));
        }
    }

    /// Shrinks the graph's data store.
    pub fn shrink_to(&mut self, nodes: usize, ports: usize) {
        self.nodes.shrink_to(nodes);
        self.ports.shrink_to(ports);
    }

    /// Changes the key of a node.
    ///
    /// It is assumed but not checked that `new_index` is currently empty.
    pub fn rekey_node(&mut self, old: NodeIndex, new: NodeIndex) {
        self.nodes.swap(old.index(), new.index());
    }

    /// Changes the key of a port.
    ///
    /// It is assumed but not checked that `new_index` is currently empty.
    pub fn rekey_port(&mut self, old: PortIndex, new: PortIndex) {
        self.ports.swap(old.index(), new.index());
    }
}

impl<N, P> Default for Weights<N, P> {
    fn default() -> Self {
        Self {
            nodes: Vec::new(),
            ports: Vec::new(),
        }
    }
}
