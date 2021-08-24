//! Module of forest/node data structures
//! This is used to construct the callgraph, but the structs are generic and
//! can be used for other purposes
//!
//! Inspired/adapted from [the example here](https://rust-leipzig.github.io/architecture/2016/12/20/idiomatic-trees-in-rust/).

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use std::collections::{BTreeSet, HashMap};

/// forest data structure
/// build from a map of IDs to nodes
/// all nodes are stored in the forest (rather than a more traditional setup where
/// the forest only has a reference to a list of roots), in order to satisfy the lifetime
/// requirements
#[derive(Default, Clone)]
pub struct Forest<U, T>
where
    T: Clone,
    U: std::hash::Hash + Eq + Clone + Ord,
{
    nodes: HashMap<U, Node<U, T>>,
}

/// node data structure
/// these are nodes in the forest
/// each node has a reference to its parents, children, and siblings
/// in addition to its data
#[derive(Default, Clone)]
pub struct Node<U, T>
where
    T: Clone,
    U: std::hash::Hash + Eq + Clone + Ord,
{
    parents: BTreeSet<U>,
    children: BTreeSet<U>,
    siblings: BTreeSet<U>,
    ind: U,

    /// the data corresponding to the node
    pub data: T,
}

/// member functions for the node struct
#[allow(unused)] // some functions aren't used here but could be used by a more general client (eg. siblings())
impl<U, T> Node<U, T>
where
    T: Clone,
    U: std::hash::Hash + Eq + Clone + Ord,
{
    /// constructor: takes the data that should be stored in the node,
    /// and its internal index ID (the ID allows it to be identified by index
    /// when searching through the forest, since this implementation of forest
    /// has a btreeset as its internal representation)
    pub fn new(data: T, ind: U) -> Self {
        Self {
            parents: BTreeSet::new(),
            children: BTreeSet::new(),
            data,
            siblings: BTreeSet::new(),
            ind,
        }
    }

    /// add a parent to the current node
    pub fn add_parent(&mut self, parent: U) {
        self.parents.insert(parent);
    }

    /// add a child to the current node
    pub fn add_child(&mut self, child: U) {
        self.children.insert(child);
    }

    /// add a list of siblings to the current node
    /// ensures that a node doesn't have a reference to itself as a sibling
    pub fn add_siblings(&mut self, siblings: BTreeSet<U>) {
        self.siblings.extend(siblings);
        self.siblings.remove(&self.ind); // just in case, remove self from siblings
    }

    /// set the data of the current node
    pub fn set_data(&mut self, data: T) {
        self.data = data;
    }

    /// get a reference to the current node's parents
    pub fn parents(&self) -> &BTreeSet<U> {
        &self.parents
    }

    /// get a reference to the current node's children
    pub fn children(&self) -> &BTreeSet<U> {
        &self.children
    }

    /// get a reference to the current node's siblings
    pub fn siblings(&self) -> &BTreeSet<U> {
        &self.siblings
    }

    /// get a reference to the current node's internal index ID
    pub fn ind(&self) -> &U {
        &self.ind
    }
}

/// member functions for the forest struct
#[allow(unused)]
impl<U, T> Forest<U, T>
where
    T: Clone,
    U: std::hash::Hash + Eq + Clone + Ord,
{
    /// constructor
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
        }
    }

    /// create a node with the specified data and ID and add it to the forest
    /// note that all nodes are added to the forest (not just root nodes) in order
    /// to satisfy the lifetime requirements
    pub fn new_node(&mut self, index: U, data: T) {
        self.nodes.insert(index.clone(), Node::new(data, index));
    }

    /// get the data of the node at a specified index
    /// returns None if the index doesn't correspond to a node
    pub fn get_data_at_index(&mut self, ind: U) -> Option<&T> {
        self.nodes.get(&ind).map(|node| &node.data)
    }

    /// set the node at a specified index
    pub fn set_node_at_index(&mut self, ind: U, node: Node<U, T>) {
        self.nodes.insert(ind, node);
    }

    /// apply the specified updates to the node at the specified index
    /// returns an error if the index does not specify a valid node
    /// updates are in the form of a NodeModStruct, that has optional updates
    /// to each field of the node
    pub fn update_node_at_index(
        &mut self,
        ind: U,
        updates: NodeModStruct<U, T>,
    ) -> Result<(), AffectErr> {
        if let Some(node) = self.nodes.get_mut(&ind) {
            if let Some(parent) = updates.parent {
                node.add_parent(parent);
            }
            if let Some(child) = updates.child {
                node.add_child(child);
            }
            if let Some(data) = updates.data {
                node.set_data(data);
            }
            if let Some(siblings) = updates.siblings {
                node.add_siblings(siblings);
            }
            Ok(())
        } else {
            Err(AffectErr::InvalidNode)
        }
    }

    /// get a reference to the nodes of the forest
    pub fn nodes(&self) -> &HashMap<U, Node<U, T>> {
        &self.nodes
    }
}

/// potential Ok states from computing the affects of a node
/// (affects refers to information propagation through the nodes)
#[derive(Debug)]
pub enum AffectOk {
    /// this node has already been (successfully) processed
    AlreadyDone,
    /// indicates successful processing
    Done,
}

/// potential Error states from computing the affects of a node
/// (affects refers to information propagation through the nodes)
#[derive(Debug)]
pub enum AffectErr {
    /// cycle detected in the graph
    /// (cycles are not necessarily always an error condition in the forest, but
    /// in some use cases it is indicative of an error so this option should be available)
    CycleDetected,
    /// invalid node specifier (e.g., ID specified that does not correspond to a forest node)
    InvalidNode,
    /// in propagating information, a node is encountered that should have already been processed
    VarNotProcessed,
    /// some invalid option specified
    InvalidOption,
}

/// enum indicating the possible directions of information flow through the forest
#[derive(Clone, Copy)]
pub enum GraphTraversalDir {
    /// propagate down the graph (through the children)
    BuiltFrom,
    /// propagate up the graph (through the parents)
    UsedToBuild,
    /// propagate along siblings
    UsedWith,
}

/// struct specifying the potential updates that can be made to a node
/// all fields are optional and, if present, in updating the node
/// this information is either:
/// * added (if a parent/child/sibling is specified)
/// * replaced (if data is specified)
pub struct NodeModStruct<U, T>
where
    U: std::hash::Hash + Eq,
    T: Clone,
{
    /// optional new parent (added to parent list)
    pub parent: Option<U>,
    /// optional new child (added to children list)
    pub child: Option<U>,
    /// optional new data (replaces the old data)
    pub data: Option<T>,
    /// optional new siblings (added to sibling list)
    pub siblings: Option<BTreeSet<U>>,
}
