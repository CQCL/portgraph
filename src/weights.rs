use crate::{NodeIndex, PortIndex};

#[derive(Debug, Clone)]
pub struct Weights<N, P> {
    nodes: Vec<N>,
    ports: Vec<P>,
}

/// Trait for graphs that encode edges connecting nodes.
/// 
/// TODO: Do a proper API design for this, and fill in the todo!s.
impl<N, P> Weights<N, P>
where N: Default, P: Default
{
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
    pub fn get_node_mut(&mut self, node: NodeIndex) -> &mut N {
        if node.index() >= self.nodes.len() {
            self.nodes.resize_with(node.index() + 1, || N::default());
        }
        &mut self.nodes[node.index()]
    }

    /// A reference to the weight of the node with a given index.
    pub fn try_get_node_mut(&mut self, node: NodeIndex) -> Option<&mut N> {
        self.nodes.get_mut(node.index())
    }

    /// A reference to the weight of the node with a given index.
    pub fn get_node(&self, _node: NodeIndex) -> &N {
        todo!()
    }

    /// Iterator over the node weights of the graph.
    pub fn node_weights(&self) -> impl Iterator<Item = &N> {
        self.nodes.iter()
    }

    /// Iterator over the node weights of the graph.
    pub fn node_weights_mut(&mut self) -> impl Iterator<Item = &mut N> {
        self.nodes.iter_mut()
    }

    /// A mutable reference to the weight of the port with a given index.
    pub fn get_port_mut(&mut self, p: PortIndex) -> &mut P {
        if p.index() >= self.ports.len() {
            self.ports.resize_with(p.index() + 1, || P::default());
        }
        &mut self.ports[p.index()]
    }

    /// A reference to the weight of the port with a given index.
    pub fn try_get_port_mut(&mut self, p: PortIndex) -> Option<&mut P> {
        self.ports.get_mut(p.index())
    }

    /// Iterator over the port weights of the graph.
    pub fn port_weights(&self) -> impl Iterator<Item = &P> {
        self.ports.iter()
    }

    /// Iterator over the port weights of the graph.
    pub fn port_weights_mut(&mut self) -> impl Iterator<Item = &mut P> {
        self.ports.iter_mut()
    }

    /// Shrinks the graph's data store.
    pub fn shrink_to(&mut self, _nodes: usize, _ports: usize) {
        todo!()
    }

    /// Changes the key of a node.
    ///
    /// It is assumed but not checked that `new_index` is currently empty.
    pub fn rekey_node(&mut self, _old: NodeIndex, _new: NodeIndex) {
        todo!()
    }

    /// Changes the key of a port.
    ///
    /// It is assumed but not checked that `new_index` is currently empty.
    pub fn rekey_port(&mut self, _old: PortIndex, _new: PortIndex) {
        todo!()
    }
}

impl<N, P> Default for Weights<N, P>
{
    fn default() -> Self {
        Self {
            nodes: Vec::new(),
            ports: Vec::new(),
        }
    }
}