//! Module with all the  functionality for building the lists of all subformulas
//! in an SMT query.
//! During this subformula listing, there is also the option of rebuilding the original
//! shape of a query after transpilation; this involves getting rid of all the new_varX
//! variables and subbing in their values where they belong in the surrounding subformulas
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{transpiler::IdentType, Command, SortExt, Term};
use amzn_smt_ir::{
    fold::{Fold, IntraLogicFolder, SuperFold},
    logic::ALL,
    CoreOp, ISort, ISymbol, IVar,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    convert::Infallible,
};

/// struct for traversing the AST and building up a list of subformulas
/// and reconstructing original shape of the query if remap_string_vars is true
#[derive(Default)]
struct StringSubformulaCountBuilder {
    /// map of variables to string function applications
    /// we'll use this to rebuild the nested function applications
    /// example: given (= x "a") and (str.prefixof x y) ==> (str.prefixof "a" y)
    string_fct_calls: HashMap<ISymbol, Term>,
    /// map of variable name to its type; we'll go through and replace it with
    /// the type in the representation for all vars that don't map to any specific string
    var_type_map: HashMap<ISymbol, IdentType>,
    /// list of all the subterms
    sub_terms: Vec<Term>,
    /// are we subbing in the values of new_varXs (to rebuild original shape of query)?
    remap_string_vars: bool,
    /// list of asserts and var decls (declarations and initializations) to
    /// get rid of if we're remapping the string vars
    remap_useless_commands: HashSet<Command>,
}

/// member functions for StringSubformulaCountBuilder
impl StringSubformulaCountBuilder {
    /// constructor, specifies whether or not we're reconstructing original query shape
    pub fn new(remap_string_vars: bool) -> Self {
        Self {
            string_fct_calls: HashMap::new(),
            var_type_map: HashMap::new(),
            sub_terms: Vec::new(),
            remap_string_vars,
            remap_useless_commands: HashSet::new(),
        }
    }

    /// function to get the list of "useless commands"; if we're reconstructing the original
    /// query shape this is the list of all the commands now subsumed in other subformulas
    pub fn remap_useless_commands(&self) -> &HashSet<Command> {
        &self.remap_useless_commands
    }
}

/// AST visitor functionality for StringSubformulaCountBuilder
impl IntraLogicFolder<ALL> for StringSubformulaCountBuilder {
    type Error = smt2parser::Error;

    /// if we are going to remap the string variables, keep track of assertions of what they're equal to
    /// also, if we are asserting a new_varX (and we're remapping the string vars), then we sub in whatever that
    /// var maps to
    fn fold_assert(&mut self, term: Term) -> Result<Command, Self::Error> {
        let mut term_to_ret = term.clone();
        let mut useless_command = false;
        // this happens before iterating into the symbols
        if self.remap_string_vars {
            match term {
                Term::CoreOp(op) => {
                    if let CoreOp::Eq(args) = op.as_ref() {
                        if let [Term::Variable(v), f @ (Term::CoreOp(..) | Term::OtherOp(..) | Term::UF(..))] =
                            args.as_slice()
                        {
                            if v.sym_str().starts_with("new_var") {
                                self.string_fct_calls.insert(v.sym().clone(), f.clone());
                                useless_command = true;
                            }
                        }
                    }
                }
                Term::Variable(v) => {
                    if let Some(new_var_sym_term) = self.string_fct_calls.get(v.sym()) {
                        term_to_ret = new_var_sym_term.clone();
                    }
                }
                _ => {}
            }
        }
        let output = term_to_ret.fold_with(self)?;
        let output = Command::Assert { term: output };
        if useless_command {
            self.remap_useless_commands.insert(output.clone());
        }
        Ok(output)
    }

    /// replace mapped variables with their corresponding terms
    fn fold_var(&mut self, v: IVar) -> Result<Term, Self::Error> {
        let output = if let Some(new_app_term) = self.string_fct_calls.get(v.sym()) {
            // fold_with to replace the var names in the term
            new_app_term.clone().fold_with(self)?
        } else {
            v.into()
        };
        Ok(output)
    }

    /// visit a function call; this happens whether or not we're remapping the string vars
    /// add all function calls to the subterm list
    fn fold_term(&mut self, t: Term) -> Result<Term, Self::Error> {
        let t = t.super_fold_with(self)?;
        // if it's a function call
        if t.op().is_some() {
            self.sub_terms.push(t.clone());
        }
        Ok(t)
    }

    /// visit all var declarations and add them to the list of vars
    /// if we're remapping string vars and this is a declaration of a new_varX, mark it as useless
    fn fold_declare_const(&mut self, symbol: ISymbol, sort: ISort) -> Result<Command, Self::Error> {
        self.var_type_map.insert(symbol.clone(), sort.get_type());

        let out = Command::DeclareConst {
            symbol: symbol.clone(),
            sort,
        };
        if self.remap_string_vars && symbol.0.starts_with("new_var") {
            self.remap_useless_commands.insert(out.clone());
        }

        Ok(out)
    }

    /// same as visit_declare_const
    /// visit all var declarations and add them to the list of vars
    /// if we're remapping string vars and this is a declaration of a new_varX, mark it as useless
    fn fold_declare_fun(
        &mut self,
        symbol: ISymbol,
        parameters: Vec<ISort>,
        sort: ISort,
    ) -> Result<Command, Self::Error> {
        self.var_type_map.insert(symbol.clone(), sort.get_type());

        let out = Command::DeclareFun {
            symbol: symbol.clone(),
            parameters,
            sort,
        };

        if self.remap_string_vars && symbol.0.starts_with("new_var") {
            self.remap_useless_commands.insert(out.clone());
        }

        Ok(out)
    }
}

/// function to reconstruct the original query shape, given a list of commands corresponding to a query
/// this involves visiting with AST with the StringSubformulaCountBuilder with the remap_string_vars option
/// set to true, to indicate that we're reconstructing the original shape
/// note: this is specifically designed to work on the output of a query transformed with the transpiler in
/// this crate; remapping the string vars is designed to work with the variable naming scheme set up
/// in this transpiler (i.e., where the new vars are indicated with new_varX)
pub fn reconstruct_orig_query_shape(commands: Vec<Command>) -> Vec<Command> {
    // if we're reconstructing, the whole point is to remap_string_vars
    let mut string_subforumla_builder = StringSubformulaCountBuilder::new(true);

    // visit the AST, finding all string function applications
    let mut output = commands
        .into_iter()
        .map(|c| c.fold_with(&mut string_subforumla_builder))
        .collect::<Result<Vec<Command>, _>>()
        .unwrap();

    // get rid of the new_varX variables
    output.retain(|c| {
        !string_subforumla_builder
            .remap_useless_commands()
            .contains(c)
    });

    output
}

/// Folder to "normalize" the variable names
/// we're going to rename them in order of appearance, to v_n (nth appearance)
/// the point: so subterms are equal over different vars
/// this only works over function applications; otherwise just returns the same term
struct VariableNameNormalizer {
    cur_vars: HashMap<ISymbol, ISymbol>,
}

impl IntraLogicFolder<ALL> for VariableNameNormalizer {
    type Error = Infallible;

    fn fold_term(&mut self, term: Term) -> Result<Term, Self::Error> {
        match term {
            Term::CoreOp(..) | Term::OtherOp(..) | Term::UF(..) => term.super_fold_with(self),
            _ => Ok(term),
        }
    }

    fn fold_var(&mut self, var: IVar) -> Result<Term, Self::Error> {
        let cur_vars = &mut self.cur_vars;
        let new = if let Some(new_name) = cur_vars.get(var.sym()) {
            new_name.clone()
        } else {
            let new_var_name: ISymbol = format!("v{}", cur_vars.len()).into();
            cur_vars.insert(var.sym().clone(), new_var_name.clone());
            new_var_name
        };
        Ok(Term::Variable(new.into()))
    }
}

/// JSON representation of a list of subformulas
#[derive(Serialize, Deserialize, Debug)]
pub struct SubFormulaJson {
    /// the list of subformulas
    pub sub_formula_list: Vec<String>,
}

/// member functions for the SubFormulaJson object
impl SubFormulaJson {
    /// constructor: takes a list of Terms and transforms it to a list of strings
    pub fn new(terms: &[Term]) -> Self {
        Self {
            sub_formula_list: terms.iter().map(|t| t.to_string()).collect::<Vec<String>>(),
        }
    }

    /// function to convert self to a pretty-printed JSON string representation
    pub fn to_json_string(&self) -> serde_json::Result<String> {
        serde_json::to_string_pretty(&self)
    }

    /// function to print self to a specified file
    pub fn print_json_to_file(&self, filename: &str) -> serde_json::Result<()> {
        let json_string = self.to_json_string()?;
        std::fs::write(filename, json_string).expect("Error in printing to file");
        Ok(())
    }
}

/// function to find the list of all subformulas in a given list of commands (representing an SMT query)
/// also takes a boolean argument specifying whether or not the original query shape will be reconstructed
/// note: this should only be true if you're reconstructing a query transpiled with the transpiler in this crate
/// if you want to find the subformula list of an arbitrary SMT query, just set this bool to false
pub fn find_string_subforumlas(
    remap_string_vars: bool,
    commands: impl Iterator<Item = Command>,
) -> Vec<Term> {
    let mut string_subforumla_builder = StringSubformulaCountBuilder::new(remap_string_vars);

    // visit the AST, finding all string function applications
    let mut output = commands
        .map(|opt_c| opt_c.fold_with(&mut string_subforumla_builder))
        .collect::<Result<Vec<Command>, _>>()
        .unwrap();

    // get rid of the new_varX variables if we're remapping string vars
    if remap_string_vars {
        output.retain(|c| {
            !string_subforumla_builder
                .remap_useless_commands()
                .contains(c)
        });
    }

    let mut normalizer = VariableNameNormalizer {
        cur_vars: HashMap::new(),
    };
    string_subforumla_builder
        .sub_terms
        .iter()
        .map(|t| {
            normalizer.cur_vars.clear();
            match t.fold_with(&mut normalizer) {
                Ok(t) => t,
                Err(e) => match e {},
            }
        })
        .collect::<Vec<Term>>()
}
