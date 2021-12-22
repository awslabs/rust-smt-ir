//! Module with all the functionality for building the callgraph, using it,
//! and propagating information through it.
//!

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use amzn_smt_ir::*;
use std::collections::{BTreeSet, HashMap, HashSet};

use crate::forest::*;
use crate::string_fcts::{StringFct, StringFctArgs};
use crate::transpiler::IdentType;

/// type alias for the node index type in the callgraph's internal forest
pub type NodeId = usize;

/// Callgraph struct.
/// This is a representation of the relationships between string function applications in
/// an SMT query.
/// Children are arguments of the parent function call; siblings are arguments to the same function.
/// All nodes in the graph are either a string function or a constraint variable.
#[derive(Clone)]
pub struct CallGraph {
    /// internal forest: all the nodes in the callgraph
    forest: Forest<NodeId, CallnodeData>,
    /// map of var names to their nodeID in the forest
    symbol_map: HashMap<ISymbol, NodeId>,
    /// set of all the nodes that correspond to constraint vars
    constraint_vars: BTreeSet<NodeId>,
    /// list of sets of nodes that are in cliques together
    /// note that these sets are not necessarily disjoint
    partitions: Vec<NodeSetData>,
    /// have we already propagated information through the graph? flag variable
    propagated: bool,
}

/// default for callgraph; all fields are empty and "propagated" is false
impl Default for CallGraph {
    fn default() -> Self {
        Self {
            forest: Forest::new(),
            symbol_map: HashMap::new(),
            constraint_vars: BTreeSet::new(),
            partitions: Vec::new(),
            propagated: false,
        }
    }
}

/// implement debug printing for callgraph
impl std::fmt::Debug for CallGraph {
    /// prints the contents of every node in the callgraph's internal forest;
    /// for each node, prints its data, parents, children, and siblings.
    /// for the data it only prints the specific string function invovled to avoid clutter
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "CallGraph: [")?;
        for (sym, node_id) in &self.symbol_map {
            let node = self.forest.nodes().get(node_id).unwrap();
            write!(f, "\tNode: {:?}", sym)?;
            write!(f, "; function: {:?}", node.data.string_fct)?;
            write!(f, "; parents: [")?;
            for pnode in node.parents() {
                write!(f, "{:?} ", pnode)?;
            }
            write!(f, "]; children: [")?;
            for cnode in node.children() {
                write!(f, "{:?} ", cnode)?;
            }
            write!(f, "]; siblings: [")?;
            for snode in node.siblings() {
                write!(f, "{:?} ", snode)?;
            }
            writeln!(f, "]")?;
        }
        write!(f, "]")
    }
}

/// Struct to store information about a set of nodes in the callgraph.
#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct NodeSetData {
    /// the set of IDs of the nodes in the set (corresponds to the set of the var each ID corresponds to)
    pub vars: BTreeSet<NodeId>,
    /// set of string functions (and their associated arguments) corresponding to the variables
    pub string_fcts: HashSet<(StringFct, StringFctArgs)>,
    /// set of string literals these variables are directly constructed from
    pub string_lits: BTreeSet<String>,
}

/// Struct to store all the data associated with a node in the callgraph; this always includes the string function
/// associated with the node (NO_OP if it's a constraint variable node), and the set of string literals directly used
/// to construct it.
/// After information propagation, this also stores the information on the sets of nodes this node is used to build, built
/// from, and used with.
#[derive(Debug, Clone)]
pub struct CallnodeData {
    /// string function associated with this node (NO_OP if it's a constraint var node)
    pub string_fct: StringFct,
    /// string literals directly used to construct this node
    pub string_lits_built_from: BTreeSet<String>,
    /// information on the nodes this node is used to build (think: transitive parents);
    /// this is None if information has not been propagated in this direction yet
    pub used_to_build: Option<NodeSetData>,
    /// information on the nodes this node is built from (think: transitive children);
    /// this is None if information has not been propagated in this direction yet
    pub built_from: Option<NodeSetData>,
    /// information on the nodes this node is used with (computed as everything this node is in a clique with);
    /// this is None if information has not been propagated in this direction yet.
    pub used_with: Option<NodeSetData>,
}

/// member functions for CallnodeData struct
impl CallnodeData {
    /// constructor: takes a string function and list of string literals.
    /// the propagated information all starts as None on node initialization
    pub fn new(sfc: StringFct, lits: BTreeSet<String>) -> Self {
        Self {
            string_fct: sfc,
            string_lits_built_from: lits,
            used_to_build: None,
            built_from: None,
            used_with: None,
        }
    }

    /// get this node's string function and associated function arguments
    pub fn get_string_fct_arg_pair(&self) -> (StringFct, StringFctArgs) {
        let elems: Vec<_> = self.string_lits_built_from.iter().cloned().collect();
        (self.string_fct, self.string_fct.get_args(&elems[..]))
    }
}

/// member functions for the Callgraph struct
impl CallGraph {
    /// get the partitions in the callgraph; recall this is the list of all nodes that are in cliques together
    /// (and there is likely overlap)
    pub fn partitions(&self) -> &[NodeSetData] {
        &self.partitions[..]
    }

    /// add a call to the callgraph; creates a new node with the variable name and callnode data specified
    /// and adds it to the internal forest.
    /// returns the ID of the newly added node
    pub fn add_call(&mut self, varname: ISymbol, cnd: CallnodeData) -> NodeId {
        let id = self.forest.nodes().len();
        self.symbol_map.insert(varname, id);
        self.forest.new_node(id, cnd);
        id
    }

    /// add a constraint variable to the internal forest; this is the same process as adding a call except it
    /// also adds the variable name to the list of constraint variables
    pub fn add_constraint_var(&mut self, varname: ISymbol, cnd: CallnodeData) -> NodeId {
        let id = self.add_call(varname, cnd);
        self.constraint_vars.insert(id);
        id
    }

    /// get the set of all node IDs that are in a partition with the given node ID.
    /// if this node doesn't appear in any partitions, this means the node is invalid (the minimum case is that
    /// a variable is in a partition with itself), so we return an invalid node error.
    fn get_all_partitions(&self, var_id: NodeId) -> Result<BTreeSet<NodeId>, AffectErr> {
        let mut all_part_nodes: BTreeSet<NodeId> = BTreeSet::new();
        // build up set of all vars this node is in a partition with
        for p in &self.partitions {
            if p.vars.contains(&var_id) {
                all_part_nodes.extend(p.vars.iter().cloned());
            }
        }
        if !all_part_nodes.is_empty() {
            Ok(all_part_nodes)
        } else {
            Err(AffectErr::InvalidNode)
        }
    }

    /// get the set of all variables that are in a partition with the given variable name.
    /// this just dispatches the internal get_all_partitions function and then constructs the set of variable names
    /// corresponding to the list of node IDs returned.
    pub fn get_constraint_vars_in_partition_with(
        &self,
        varname: &ISymbol,
    ) -> Result<Vec<ISymbol>, AffectErr> {
        let var_id = self.symbol_map.get(varname);
        if matches!(var_id, None) {
            return Err(AffectErr::InvalidNode);
        }
        let var_id = var_id.unwrap();
        let all_partition = self.get_all_partitions(*var_id)?;
        let constraint_var_ids = self.constraint_vars.intersection(&all_partition);
        Ok(constraint_var_ids
            .map(|v_id| self.get_sym_for_id(*v_id).unwrap().clone())
            .collect::<Vec<_>>())
    }

    /// add a parent/child relationship to the callgraph.
    /// throws an error if either of the nodes are invalid
    pub fn add_parent_child(
        &mut self,
        parent_var: &ISymbol,
        child_var: &ISymbol,
    ) -> Result<(), AffectErr> {
        let parent_id = self.symbol_map.get(parent_var);
        let child_id = self.symbol_map.get(child_var);
        if matches!((parent_id, child_id), (_, None) | (None, _)) {
            // invalid call node specified
            return Err(AffectErr::InvalidNode);
        }

        // update parent with new child
        self.forest.update_node_at_index(
            *parent_id.unwrap(),
            NodeModStruct::<NodeId, CallnodeData> {
                parent: None,
                child: Some(*child_id.unwrap()),
                siblings: None,
                data: None,
            },
        )?;
        // update child with new parent
        self.forest.update_node_at_index(
            *child_id.unwrap(),
            NodeModStruct::<NodeId, CallnodeData> {
                parent: Some(*parent_id.unwrap()),
                child: None,
                siblings: None,
                data: None,
            },
        )?;
        Ok(())
    }

    /// add sibling relationships to the callgraph. every node in the specified set gets every other node in the set
    /// added as direct siblings.
    /// the list of string literals passed in are the string literal siblings of all these nodes.
    pub fn add_direct_siblings(
        &mut self,
        siblings: BTreeSet<ISymbol>,
        sib_strings: BTreeSet<String>,
    ) -> Result<(), AffectErr> {
        // build up the list of sibling IDs
        let mut sib_ids: BTreeSet<NodeId> = BTreeSet::new();
        for sib in &siblings {
            match self.symbol_map.get(sib) {
                Some(sib_id) => {
                    sib_ids.insert(*sib_id);
                }
                None => {
                    return Err(AffectErr::InvalidNode); // node doesn't exist
                }
            }
        }
        // update siblings with the new sibling nodes, and new sibling strings
        for sib_id in &sib_ids {
            self.forest.update_node_at_index(
                *sib_id,
                NodeModStruct::<NodeId, CallnodeData> {
                    parent: None,
                    child: None,
                    siblings: Some(sib_ids.clone()),
                    data: if !sib_strings.is_empty() {
                        // adding to the string_lits_built_from
                        Some(CallnodeData::new(StringFct::NO_OP, sib_strings.clone()))
                    } else {
                        None
                    },
                },
            )?;
        }
        Ok(())
    }

    /// get the callnode data for the variable name specified (error if there's no valid node for this variable)
    pub fn get_data_for_var(&self, var: &ISymbol) -> Result<&CallnodeData, AffectErr> {
        match self.symbol_map.get(var) {
            Some(var_id) => self.get_data_for_ind(var_id),
            None => Err(AffectErr::InvalidNode),
        }
    }

    /// get the callnode data for the node ID specified (error if there is no valid node for this ID)
    pub fn get_data_for_ind(&self, var: &NodeId) -> Result<&CallnodeData, AffectErr> {
        match self.forest.nodes().get(var) {
            Some(n) => Ok(&n.data),
            None => Err(AffectErr::InvalidNode),
        }
    }

    /// get the variable name for the specified node ID (None if there is no node with this ID)
    pub fn get_sym_for_id(&self, var_id: NodeId) -> Option<&ISymbol> {
        self.symbol_map
            .iter()
            .find_map(|(sym, &id)| if id == var_id { Some(sym) } else { None })
    }

    /// get the node ID for the variable name specified (None if there is no node ID matching this name)
    pub fn get_id_for_sym(&self, sym: &ISymbol) -> Option<&NodeId> {
        self.symbol_map.get(sym)
    }

    /// function to build up information about the children or parents.
    /// this propagates through the graph either up/down until it hits a StringFct where the info is lost (
    /// i.e. a string function through which information is not propagated)
    fn propagate_along_path(
        &mut self,
        var: NodeId,
        direction: GraphTraversalDir,
    ) -> Result<(NodeSetData, AffectOk), AffectErr> {
        let nodes = self.forest.nodes().clone();
        let cur_node = match nodes.get(&var) {
            Some(n) => n,
            None => {
                // if the node is not in the callgraph, error out
                return Err(AffectErr::InvalidNode);
            }
        };

        // if already done, bail early
        // this means we will never re-propagate, if we're collecting from
        // a node we've already collected from, just return this data
        // this keeps the alg linear in the size of the graph
        match direction {
            GraphTraversalDir::BuiltFrom => {
                // children
                if let Some(contrib) = &cur_node.data.built_from {
                    return Ok((contrib.clone(), AffectOk::AlreadyDone));
                }
                self.propagate_through_relnodes(var, cur_node.children(), &cur_node.data, direction)
            }
            GraphTraversalDir::UsedToBuild => {
                // parents
                if let Some(contrib) = &cur_node.data.used_to_build {
                    return Ok((contrib.clone(), AffectOk::AlreadyDone));
                }
                self.propagate_through_relnodes(var, cur_node.parents(), &cur_node.data, direction)
            }
            _ => Err(AffectErr::InvalidOption),
        }
    }

    /// function to actually propagate through the nodes passed in from the propagate_along_path function
    fn propagate_through_relnodes(
        &mut self,
        var: NodeId,
        rel_nodes: &BTreeSet<NodeId>,
        cur_data: &CallnodeData,
        direction: GraphTraversalDir,
    ) -> Result<(NodeSetData, AffectOk), AffectErr> {
        // now the work begins

        // definitely take current literals and immediate neighbour nodes (in the direction specified)
        // then, depending on the type of each node, recurse back
        // need to keep track to detect cycles (if there is one, bail with a cycle error)
        let mut contrib_vars = rel_nodes.iter().cloned().collect::<BTreeSet<_>>();

        // if the nodes include the var itself, cycle detected
        if contrib_vars.contains(&var) {
            return Err(AffectErr::CycleDetected);
        }
        let mut contrib_string_fcts = HashSet::<(StringFct, StringFctArgs)>::new();
        contrib_string_fcts.insert(cur_data.get_string_fct_arg_pair());

        let mut contrib_string_lits = cur_data
            .string_lits_built_from
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();

        let rel_nodes = rel_nodes.iter().cloned().collect::<BTreeSet<_>>();

        // now actually collect the data from the relevant nodes
        for node in rel_nodes {
            if let Some(node) = self.forest.nodes().get(&node) {
                contrib_string_fcts.insert(node.data.get_string_fct_arg_pair());
                // information doesn't propagate through functions that return a Bool
                if matches!(
                    node.data.string_fct.string_fct_return_type(),
                    IdentType::StringType
                        | IdentType::RegexStringType
                        | IdentType::IntType // int also requires the string chars potentially
                        | IdentType::ConstraintVarType
                ) {
                    let cur_ind = *node.ind();
                    let node_contribs_res = self.propagate_along_path(cur_ind, direction);
                    if let Ok((node_contribs, _)) = node_contribs_res {
                        contrib_vars.extend(node_contribs.vars.iter().cloned());
                        // check again for cycles
                        if contrib_vars.contains(&var) {
                            return Err(AffectErr::CycleDetected);
                        }
                        contrib_string_fcts.extend(node_contribs.string_fcts);
                        contrib_string_lits.extend(node_contribs.string_lits);
                    } else {
                        // if there was an error in processing the affects of rel_node, bail with this error
                        return node_contribs_res;
                    }
                }
            } else {
                // rel_node is not found in the callgraph
                return Err(AffectErr::InvalidNode);
            }
        }

        // finally, once the data has all been collected, update the current node with the contribs
        let new_node_data = cur_data.clone();
        let new_nodeset_data = NodeSetData {
            vars: contrib_vars,
            string_fcts: contrib_string_fcts,
            string_lits: contrib_string_lits,
        };
        self.update_node_with_contribs(var, new_nodeset_data.clone(), new_node_data, direction)?;
        Ok((new_nodeset_data, AffectOk::Done))
    }

    /// get the nodesetdata representing all the nodes (and their associated string functions and string literals)
    /// that "contribute" to the specified node.
    /// "contribute" here means that it is in a partition with the specified node (so, used_with).
    /// returns None if there is no partition with the specified node ID.
    fn get_contribs_for_var(&self, var: NodeId) -> Option<NodeSetData> {
        let mut to_ret = NodeSetData::default();
        for cur_partition in &self.partitions {
            if cur_partition.vars.contains(&var) {
                to_ret.vars.extend(cur_partition.vars.clone());
                to_ret.string_fcts.extend(cur_partition.string_fcts.clone());
                to_ret.string_lits.extend(cur_partition.string_lits.clone());
            }
        }
        if !to_ret.vars.is_empty() {
            Some(to_ret)
        } else {
            None
        }
    }

    /// propagate information in the "used_with" direction; i.e. through the cliques.
    fn propagate_used_with(
        &mut self,
        var: NodeId,
        cliques: &HashMap<NodeId, NodeSetData>,
    ) -> Result<(NodeSetData, AffectOk), AffectErr> {
        let nodes = self.forest.nodes().clone();
        let cur_node = match nodes.get(&var) {
            Some(n) => n,
            None => {
                // if the node is not in the callgraph, error out
                return Err(AffectErr::InvalidNode);
            }
        };

        // if already done, bail early
        if let Some(contrib) = &cur_node.data.used_with {
            return Ok((contrib.clone(), AffectOk::AlreadyDone));
        }

        // if it's in a partition we've already formed, just collect this
        if let Some(contrib) = self.get_contribs_for_var(var) {
            self.update_node_with_contribs(
                var,
                contrib.clone(),
                cur_node.data.clone(),
                GraphTraversalDir::UsedWith,
            )?;
            return Ok((contrib, AffectOk::AlreadyDone));
        }

        // now, we're tracking the literals, vars, and string functions that the current var are used WITH
        // these are all the nodes that are in cliques with the current var

        let mut contrib_vars = BTreeSet::<NodeId>::new();
        contrib_vars.insert(var);
        let mut contrib_string_fcts = HashSet::<(StringFct, StringFctArgs)>::new();
        contrib_string_fcts.insert(cur_node.data.get_string_fct_arg_pair());
        let mut contrib_string_lits: BTreeSet<String> =
            cur_node.data.string_lits_built_from.clone();

        // iterate over the cliques and collect the info from those who contain the current var
        let mut cids: Vec<&NodeId> = cliques.keys().collect::<Vec<_>>();
        cids.sort();

        for cid in cids {
            let clique = &cliques[cid];
            if clique.vars.contains(&var) {
                contrib_vars.extend(clique.vars.iter().cloned());
                contrib_string_fcts.extend(clique.string_fcts.iter().cloned());
                contrib_string_lits.extend(clique.string_lits.iter().cloned());
            }
        }

        // finally, once the data has all been collected, update the current node with the contribs
        let new_node_data = cur_node.data.clone();
        let new_nodeset_data = NodeSetData {
            vars: contrib_vars,
            string_fcts: contrib_string_fcts,
            string_lits: contrib_string_lits,
        };
        self.update_node_with_contribs(
            var,
            new_nodeset_data.clone(),
            new_node_data,
            GraphTraversalDir::UsedWith,
        )?;
        self.partitions.push(new_nodeset_data.clone());
        Ok((new_nodeset_data, AffectOk::Done))
    }

    /// function to update a given node with the contributions (in the form of NodeSetData)
    /// in the graph traversal direction specified.
    /// the CallnodeData passed in will be updated with the contribution in the traversal direction
    /// specified, and then this is passed in as an update to the specified node.
    fn update_node_with_contribs(
        &mut self,
        var: NodeId,
        new_nodeset_data: NodeSetData,
        mut new_node_data: CallnodeData,
        direction: GraphTraversalDir,
    ) -> Result<(), AffectErr> {
        match direction {
            GraphTraversalDir::BuiltFrom => {
                new_node_data.built_from = Some(new_nodeset_data);
            }
            GraphTraversalDir::UsedToBuild => {
                new_node_data.used_to_build = Some(new_nodeset_data);
            }
            GraphTraversalDir::UsedWith => {
                new_node_data.used_with = Some(new_nodeset_data);
            }
        }

        self.forest.update_node_at_index(
            var,
            NodeModStruct::<NodeId, CallnodeData> {
                parent: None,
                child: None,
                data: Some(new_node_data),
                siblings: None,
            },
        )?;
        Ok(())
    }

    /// function to construct all the cliques in the callgraph.
    /// for each constraint var, we construct a clique of linked nodes in the graph
    /// this is the set of, for each constraint var cvar,
    ///       everything that was used_to_build what cvar was used_to_build
    /// computed as: foreach var in cvar.used_to_build:
    ///                  collect var.built_from
    ///
    /// note: this *needs* to happen after the information has been propagated both up and
    /// down the graph; if we hit a node that doesn't have built_from or used_to_build sets
    /// computed we bail with a VarNotProcessed error
    fn propagate_constraint_var_cliques(
        &mut self,
    ) -> Result<HashMap<NodeId, NodeSetData>, AffectErr> {
        let mut constraint_cliques: HashMap<NodeId, NodeSetData> =
            HashMap::with_capacity(self.constraint_vars.len());
        for cvar in &self.constraint_vars {
            if let Some(cvar_utbs) = &self.get_data_for_ind(cvar)?.used_to_build {
                let mut clique_vars: BTreeSet<NodeId> =
                    cvar_utbs.vars.iter().cloned().collect::<BTreeSet<_>>();
                let mut clique_string_fcts: HashSet<(StringFct, StringFctArgs)> = cvar_utbs
                    .string_fcts
                    .iter()
                    .cloned()
                    .collect::<HashSet<_>>();
                let mut clique_string_lits: BTreeSet<String> = cvar_utbs
                    .string_lits
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>();
                for utb_var in &cvar_utbs.vars {
                    if let Some(utb_bfs) = &self.get_data_for_ind(utb_var)?.built_from {
                        clique_vars.extend(utb_bfs.vars.iter().cloned());
                        clique_string_fcts.extend(utb_bfs.string_fcts.iter().cloned());
                        clique_string_lits.extend(utb_bfs.string_lits.iter().cloned());
                    } else {
                        return Err(AffectErr::VarNotProcessed);
                    }
                }
                constraint_cliques.insert(
                    *cvar,
                    NodeSetData {
                        vars: clique_vars,
                        string_fcts: clique_string_fcts,
                        string_lits: clique_string_lits,
                    },
                );
            } else {
                return Err(AffectErr::VarNotProcessed);
            }
        }
        Ok(constraint_cliques)
    }

    /// propagate information in all directions through the graph; first up/down the graph,
    /// then we compute the cliques and propagate through those.
    /// if the information has already been propagated we don't recompute everything.
    pub fn propagate_all(&mut self) -> Result<(), AffectErr> {
        if self.propagated {
            return Ok(());
        }
        let nodes = self.forest.nodes().clone();
        for (key, _node) in nodes.iter() {
            self.propagate_along_path(*key, GraphTraversalDir::UsedToBuild)?;
            self.propagate_along_path(*key, GraphTraversalDir::BuiltFrom)?;
        }
        let cliques = self.propagate_constraint_var_cliques()?;
        for (key, _node) in nodes.iter() {
            // this needs to happen after the parents/children are collected
            self.propagate_used_with(*key, &cliques)?;
        }
        self.propagated = true;
        Ok(())
    }
}
