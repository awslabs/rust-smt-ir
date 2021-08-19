//! This is a tool for canonicalizing the strings in SMT string constraints, while
//! maintaining equisatisfiability of the queries.
//!
//! ### High-level overview
//! There are many reasons that users might want to transform SMT formulae (anonymization, canonicalization,
//! compression, ...).
//! In order to guarantee equisatisfiability we must be careful of how the string literals being transformed
//! interact with the constraints.  
//! In this tool, we model this as a dataflow problem, and construct a callgraph of an SMT query to track relationships
//! between string functions and their arguments -- the callgraph functionality is included in the [`callgraph`] module,
//! and the construction of the callgraph is done through visiting the AST of the SMT query, in the [`transpiler_visitors`]
//! module.
//! With this callgraph and our type-based model of functions and the string properties that they require be maintained,
//! we present a framework for performing equisatisfiable transformations on the string literals of SMT queries --
//! this type-based tracking of properties is included in the [`string_fcts`] module.
//! We also build and present one possible string mapping function, included in the [`string_mappings`] module.
//!
//! The other main module to keep note of is [`transpiler`], which includes the driver function for applying
//! the transformation, [`transpiler::transform_ast`].
//!
//! ### Usage
//! Once there is a built binary of this crate, it can be called with various command line options to
//! specify how the SMT files should be transformed.
//! ```bash
//! // general case
//! <built binary> --input-file <path to file to convert> --mode convert --mapping <mapping type> --use-global-map <boolean>
//!
//! // specific example
//! <built binary> --input-file ex1.smtlib --mode convert --mapping no-reconstruct --use-global-map false
//! ```
//! This generates a transformed file, `<path to file to convert, without file extension>_transformed.smtlib`.
//! For example, running with `ex1.smtlib` generates the transformed file `ex1_transformed.smtlib`.
//!
//! It also generates a mapping file, `<path to file to convert, without file extension>_mapping.json`.
//! This file contains the following information:
//! * character mapping: what characters in the original query map to in the transformed query (if the `char-to-char` mapping option was used)
//! * string mapping: what string literals in the original query map to in the transformed query
//! * variable mapping: what constraint variables in the original query get renamed to in the transformed query
//! * list of constraint variables affected by the transformation (this is the list of variables whose solutions are remapped if you choose to reconstruct)
//! * variables failing to map: variables that use an unsupported string function. If this list is non-empty then the transformation will fail and the output SMTLIB file will contain an error message "Encountered unsupported string function: BAILING OUT".
//! * persistent string map: essentially an extended version of the string mapping, this has metadata about the substrings and string properties invovled in the transformation of each string literal.
//! This is needed if the `use-global-map` option is true (in this case, mappings are reused for future queries, and so this extra context is required to see if a mapping is valid).

#![warn(rust_2018_idioms)]
#![warn(missing_docs)]

pub mod callgraph;
pub mod forest;
pub mod mapping_tools;
pub mod reconstruct_tools;
pub mod string_fcts;
pub mod string_mappings;
pub mod subformula_parser;
pub mod transpiler;
pub mod transpiler_visitors;

use amzn_smt_ir::{logic::ALL, Command as IRCommand, Term as IRTerm};
use transpiler::IdentType;

type Term = IRTerm<ALL>;
type Command = IRCommand<Term>;

/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/// extension to Sort; adds a member function that gets the corresponding IdentType
/// (basically, converting the Sort into my custom types)
trait SortExt {
    /// get the IdentType corresponding to the Sort
    fn get_type(&self) -> IdentType;
}

/// implement the SortExt trait for Sort; this adds access to the get_type member function
impl SortExt for amzn_smt_ir::Sort {
    /// get the IdentType corresponding to the Sort
    fn get_type(&self) -> IdentType {
        match self.sym_str() {
            "Bool" => IdentType::BoolType,
            "String" => IdentType::StringType,
            "Int" => IdentType::IntType,
            "RegLan" => IdentType::RegexStringType,
            _ => IdentType::UnknownType,
        }
    }
}
