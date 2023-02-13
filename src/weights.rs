use crate::{NodeIndex, PortIndex};

#[derive(Debug, Clone)]
pub struct Weights<N, P> {
    nodes: Vec<NodeWeight<N>>,
    ports: Vec<PortWeight<P>>,
}

#[derive(Default, Debug, Clone)]
struct NodeWeight<N> (N);

#[derive(Default, Debug, Clone)]
struct PortWeight<P> (P);

/// Trait for graphs that encode edges connecting nodes.
///
/// TODO: Do a proper API design for this, and fill in the todo!s.
impl<N, P> Weights<N, P>
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
    pub fn get_node_mut(&mut self, node: NodeIndex) -> &mut N
        where N: Default {
        if node.index() >= self.nodes.len() {
            self.nodes.resize_with(node.index() + 1, || Default::default());
        }
        &mut self.nodes[node.index()].0
    }

    /// A reference to the weight of the node with a given index.
    pub fn try_get_node_mut(&mut self, node: NodeIndex) -> Option<&mut N> {
        self.nodes.get_mut(node.index()).map(|p| &mut p.0)
    }

    /// A reference to the weight of the node with a given index.
    pub fn get_node(&self, _node: NodeIndex) -> &N where N: Default {
        todo!()
        //&self.nodes.get(node.index()).unwrap_or(&NodeWeight::DEFAULT).0
    }

    /// A reference to the weight of the node with a given index.
    pub fn try_get_node(&self, node: NodeIndex) -> Option<&N> {
        self.nodes.get(node.index()).map(|n| &n.0)
    }

    /// A mutable reference to the weight of the port with a given index.
    pub fn get_port_mut(&mut self, p: PortIndex) -> &mut P where P: Default{
        if p.index() >= self.ports.len() {
            self.ports.resize_with(p.index() + 1, || Default::default());
        }
        &mut self.ports[p.index()].0
    }

    /// A reference to the weight of the port with a given index.
    pub fn try_get_port_mut(&mut self, p: PortIndex) -> Option<&mut P> {
        self.ports.get_mut(p.index()).map(|p| &mut p.0)
    }

    /// A reference to the weight of the port with a given index.
    pub fn get_port(&self, _port: PortIndex) -> &P where P: Default {
        todo!()
        //&self.ports.get(port.index()).unwrap_or(&PortWeight::DEFAULT).0
    }

    /// A reference to the weight of the port with a given index.
    pub fn try_get_port(&self, port: PortIndex) -> Option<&P> {
        self.ports.get(port.index()).map(|p| &p.0)
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
