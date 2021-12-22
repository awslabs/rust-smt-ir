//! Module with all the visitors/AST traversal functionality required for the main
//! transpiler.
//!
//! We are using the [smt2parser crate](https://docs.rs/smt2parser/0.3.0/smt2parser/) to parse the SMT queries
//! and traverse the AST.
//! The source for all the shapes of AST elements in this crate is found
//! [here](https://github.com/facebookincubator/smt2utils/blob/master/smt2parser/src/concrete.rs).

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use amzn_smt_ir::args::Arguments;
use amzn_smt_ir::fold::{IntraLogicFolder, SuperFold};
use amzn_smt_ir::logic::ALL;
use amzn_smt_ir::{CoreOp, IConst, ISort, ISymbol, IVar};
use smt2parser::concrete::*;
use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::convert::Infallible;

use crate::{callgraph::*, string_fcts::*, transpiler::*, Command, SortExt, Term};

/// Extension on the smt2parser SyntaxBuilder; adding fields for the things we need to keep track of
/// during the AST traversal.
/// This is the first-pass parser, where we construct the list of all string vars, the callgraph etc
#[derive(Default)]
pub struct IdentifyStringsBuilder {
    /// list of string vars; need to keep track to see if equality is over string vars
    pub string_var_list: BTreeSet<ISymbol>,
    /// map of terms (spec. string function applications) and the new vars introduced to represent them
    const_map: HashMap<Term, ISymbol>,
    /// list of ALL constant decls
    /// we're lifting these all to the top of the program to make sure that any newly created vars
    /// are initalized after the vars they might make use of
    /// another solution would be to add the decls in place, but this is quick-and-dirty and seems just as good
    pub decl_const_list: Vec<Command>,
    /// list of newly created assertions (i.e., initializing the new vars we introduce)
    pub assert_list: Vec<Command>,
    /// map of a string variable to its generated assert statement (think: variable definition)
    /// this contains the function call that defines the var, which is where we find all the string
    /// literals available for simplification
    pub string_var_defn_map: HashMap<ISymbol, Term>,
    /// hashset of all string constants
    string_consts: BTreeSet<String>,
    /// build the callgraph as we visit the whole AST
    pub callgraph: CallGraph,
    /// mapping of symbols to new symbols (for alpha renaming)
    pub alpha_renaming_map: HashMap<ISymbol, ISymbol>,
    /// list of original constraint variables that appear in a context that implies
    /// that all characters in string literals used with are all characters need to be respected
    pub char_level_substring_vars: HashSet<ISymbol>,
}

/// member functions for the IdentifyStringsBuilder struct
impl IdentifyStringsBuilder {
    /// create the decl-const for a new var with the specified name
    fn new_var_decl_const(new_var_name: ISymbol, new_var_type: IdentType) -> Command {
        let new_sort = Sort::Simple {
            identifier: Identifier::Simple {
                symbol: Symbol(new_var_type.to_string()),
            },
        }
        .into();

        Command::DeclareConst {
            symbol: new_var_name,
            sort: new_sort,
        }
    }

    /// inspect the term parameters (if any), and attach the parent/child in the callgraph
    /// also initialize direct siblings in the args
    fn inspect_parameters(&mut self, var_sym: ISymbol, t: &Term, sfc: StringFct) {
        if let Some(op) = t.op() {
            let mut ident_args = BTreeSet::new();
            // also track the string literal siblings; these contribute to what a node is built_from
            let mut string_lits = BTreeSet::<String>::new();
            self.char_level_substring_vars
                .extend(char_level_substrings_required(
                    op.args()
                        .into_iter()
                        .cloned()
                        .collect::<Vec<Term>>()
                        .as_slice(),
                    sfc,
                    &self.alpha_renaming_map,
                ));
            for arg in op.args() {
                if let Term::Variable(identifier) = arg {
                    let ident_sym = identifier.sym();
                    if self.string_var_list.contains(&ident_sym.clone()) {
                        ident_args.insert(ident_sym.clone());
                        self.callgraph.add_parent_child(&var_sym, ident_sym).ok();
                    }
                } else if let Term::Constant(c) = arg {
                    if let Constant::String(s) = c.as_ref() {
                        string_lits.insert(s.clone());
                    }
                }
            }
            self.callgraph
                .add_direct_siblings(ident_args, string_lits)
                .ok();
        }
    }

    /// process a string function application: if it's not already computed,
    /// then make a new var and add new decl-const and asserts where needed
    /// for example:
    /// (assert (= v0 (str.prefixof "hello-prefix:string" v1)))
    /// turns into
    /// (declare-const new_var String)
    /// (assert (= new_var (str.prefixof "hello-prefix:string" v1)))
    /// (assert (= v0 new_var))
    fn process_string_fct(&mut self, sfc: StringFct, t: &Term) -> Option<ISymbol> {
        let mut string_const_args = BTreeSet::<String>::new();
        // build up all the string constant args, and use this to check for non-string equality
        let mut non_string_arguments = false;
        if let Some(op) = t.op() {
            for arg in op.args() {
                if let Term::Constant(c) = arg {
                    if let Constant::String(s) = c.as_ref() {
                        string_const_args.insert(s.to_string());
                        continue;
                    }
                } else if let Term::Variable(v) = arg {
                    non_string_arguments |= !self.string_var_list.contains(v.sym());
                    continue;
                }
                non_string_arguments = true;
            }
        }
        if non_string_arguments && sfc == StringFct::StrEquality {
            // if it's equality, it might not be over strings
            // only proceed if all args are strings or some of our created string vars
            return None;
        }

        // add new_var to the list of new vars, storing this string function
        let len = self.const_map.len();
        let var_sym = match self.const_map.entry(t.clone()) {
            Entry::Occupied(o) => o.get().clone(),
            Entry::Vacant(v) => {
                let new_var_type = sfc.string_fct_return_type();
                let new_var_name = ISymbol::from(format!("new_var{}", len));
                self.decl_const_list
                    .push(Self::new_var_decl_const(new_var_name.clone(), new_var_type));
                self.string_var_defn_map
                    .insert(new_var_name.clone(), t.clone());
                self.assert_list
                    .push(new_assert_equal(new_var_name.clone(), t));
                self.string_var_list.insert(new_var_name.clone());
                v.insert(new_var_name.clone());
                new_var_name
            }
        };
        self.callgraph
            .add_call(var_sym.clone(), CallnodeData::new(sfc, string_const_args));
        // inspect the term parameters (if any), and map any string var params
        // to the current string var (add parent/child to the callgraph)
        self.inspect_parameters(var_sym.clone(), t, sfc);

        Some(var_sym)
    }
}

/// create the assertion for a new var (think: variable initialization)
/// example: given "new_var1" and term t, this creates an assertion
/// (assert (= new_var1 t))
pub fn new_assert_equal(new_var_name: ISymbol, t: &Term) -> Command {
    let term = CoreOp::Eq([Term::Variable(new_var_name.into()), t.clone()].into()).into();
    Command::Assert { term }
}

/// Implement visitors for the relevant AST elements for the IdentifyStringsBuilder
///
/// For example visitors, see
/// [this example](https://github.com/facebookincubator/smt2utils/blob/master/smt2parser/src/rewriter.rs#L841).
impl IntraLogicFolder<ALL> for IdentifyStringsBuilder {
    type Error = smt2parser::Error;

    /// visit function applications
    /// if the function being applied is one of the string function, then it is
    /// processed accordingly
    fn fold_term(&mut self, t: Term) -> Result<Term, Self::Error> {
        let t = t.super_fold_with(self)?;
        if let Some(sfc) = t.op().and_then(|op| op.func().string_fct()) {
            match self.process_string_fct(sfc, &t) {
                Some(new_var_sym) => {
                    // now, replace the string function term with the new var
                    Ok(Term::Variable(new_var_sym.into()))
                }
                None => Ok(t),
            }
        } else {
            Ok(t)
        }
    }

    /// visit constant declarations
    /// these are all the original variables in the query
    /// rename them to aX (where X is an int referring to this being the nth var declared)
    fn fold_declare_const(&mut self, symbol: ISymbol, sort: ISort) -> Result<Command, Self::Error> {
        let new_var_name = format!("a{}", self.alpha_renaming_map.len());
        let new_sym = ISymbol::from(new_var_name);
        self.alpha_renaming_map.insert(symbol, new_sym.clone());

        // if it's a string var add it to the list of string vars and the callgraph
        if sort.get_type() == IdentType::StringType {
            self.string_var_list.insert(new_sym.clone());
            let _var_id = self.callgraph.add_constraint_var(
                new_sym.clone(),
                CallnodeData::new(StringFct::NO_OP, BTreeSet::new()),
            );
        }
        let out = Command::DeclareConst {
            symbol: new_sym,
            sort,
        };
        self.decl_const_list.push(out.clone());
        Ok(out)
    }

    /// basically the same as visiting constant declarations
    fn fold_declare_fun(
        &mut self,
        symbol: ISymbol,
        parameters: Vec<ISort>,
        sort: ISort,
    ) -> Result<Command, Self::Error> {
        let new_var_name = format!("a{}", self.alpha_renaming_map.len());
        let new_sym = ISymbol::from(new_var_name);
        self.alpha_renaming_map.insert(symbol, new_sym.clone());

        // if it's a string var add it to the list of string vars and the callgraph
        if sort.get_type() == IdentType::StringType {
            self.string_var_list.insert(new_sym.clone());
            let _var_id = self.callgraph.add_constraint_var(
                new_sym.clone(),
                CallnodeData::new(StringFct::NO_OP, BTreeSet::new()),
            );
        }
        let out = Command::DeclareFun {
            symbol: new_sym,
            parameters,
            sort,
        };
        self.decl_const_list.push(out.clone());
        Ok(out)
    }

    /// visit symbols
    /// if the symbol is one of the variables we have renamed, then
    /// replace it with the new name
    fn fold_var(&mut self, v: IVar) -> Result<Term, Self::Error> {
        if let Some(sym) = self.alpha_renaming_map.get(v.sym()) {
            return Ok(sym.clone().into());
        }
        Ok(v.into())
    }

    /// visit constants
    /// if it's a string constant, add it to the list of string constants
    fn fold_const(&mut self, constant: IConst) -> Result<Term, Self::Error> {
        if let Constant::String(s) = constant.as_ref() {
            self.string_consts.insert(s.clone());
        }
        Ok(Term::Constant(constant))
    }
}

/// Another extension on the SyntaxBuilder; this is for the second round parsing,
/// where we actually do the simplification of strings.
/// Now we have fields for storing the info from the first parsing pass that we need to check when converting strings.
pub struct SimplifyStringsBuilder {
    /// map of all terms to replace, and their replacements
    replaced_terms: HashMap<Term, Term>,
}

/// member functions on the SimplifyStringsBuilder
impl SimplifyStringsBuilder {
    /// constructor: takes a map of terms to be replaced and what they should be replaced with.
    pub fn new(replaced_terms: HashMap<Term, Term>) -> Self {
        Self { replaced_terms }
    }
}

/// Implementing visitors for the SimplifyStringsBuilder.
/// This just visits all application term and replaces them if they're in the map of terms to be replaced.
impl IntraLogicFolder<ALL> for SimplifyStringsBuilder {
    type Error = Infallible;

    /// visit function applications; replace them if they're in the list of terms to be replaced.
    /// note that all terms to be replaced are going to be function applications.
    fn fold_term(&mut self, t: Term) -> Result<Term, Self::Error> {
        match self.replaced_terms.get(&t) {
            Some(new_term) => Ok(new_term.clone()),
            None => t.super_fold_with(self),
        }
    }
}

/// extension to QualIdentifier; adds member functions for converting to/from symbols and for
/// getting the string function corresponding to this symbol (if applicable)
///
/// thanks max!
trait SymbolExt {
    /// return the string function corresponding to the symbol this qualident represents (if applicable)
    fn string_fct(&self) -> Option<StringFct>;
}
impl SymbolExt for Symbol {
    /// get corresponding string function, if applicable
    fn string_fct(&self) -> Option<StringFct> {
        let s = self.0.as_str();
        for (sf, sfc) in STRING_FCTS.iter() {
            if s == *sf {
                return Some(*sfc);
            };
        }
        None
    }
}
