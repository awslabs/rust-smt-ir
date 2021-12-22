//! Module of structs/functions used for reconstructing a satisfying solution for a
//! problem given a satisfying solution for the transpiled version of the same problem
//! note that this only works if the transpilation has been done using the char-to-char
//! option
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{mapping_tools, Command, Term};
use amzn_smt_ir::{FunctionDec, ISymbol};
use smt2parser::concrete::*;
use smt2parser::CommandStream;
use std::collections::HashMap;
use std::{fs, io, io::BufRead};

/// enum of possible acceptable results from running a solver on an attempted reconstruction
/// (recall: "reconstruction" refers to the addition of assertions of the unmapped satisfying solutions
/// to the original problem. these results are all the valid solver outputs)
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ReconstructResult {
    /// result is SAT, but no model was produced
    SatNoModel,
    /// result is UNSAT
    Unsat,
    /// result is SAT and a model was produced
    SatModelBuilt,
    /// timeout
    Timeout,
    /// result is Unknown
    Unknown,
}

/// enum of possible errors from an attempted reconstruction
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ReconstructErr {
    /// error reading the corresponding mapping file (reconstruction only possible after mapping is output)
    MappingFileReadError,
    /// unexpected shape of output of running the solver on the transpiled query (this output is parsed)
    UnexpectedTransformedModelParse,
    /// error reading the output of running the solver on the transpiled query
    TransformOutputFileReadError,
    /// (check-sat) was not found in the original query, leading to no result after running the solver
    CheckSatNotFound,
}

/// function to add a list of assertions to an SMT query in a file at a path specified
fn add_asserts_to_original_problem(
    path: String,
    ext: String,
    new_assertions: Vec<Command>,
) -> Result<String, ReconstructErr> {
    let file = fs::File::open(path + "." + &ext).expect("Error reading in original problem");
    let reader = io::BufReader::new(file);
    let problem = CommandStream::new(reader, SyntaxBuilder, None);

    let mut check_sat_found = false;

    let mut commands: Vec<Command> = Vec::new();
    for opt_c in problem {
        let c = opt_c.unwrap_or_else(|err| panic!("ERROR in command: {:?}", err));
        let c = amzn_smt_ir::convert::convert_command(c).unwrap();
        // make sure to add the new assertions before the check-sat
        if let Command::CheckSat = c {
            check_sat_found = true;
            commands.extend(new_assertions.clone());
        }
        commands.push(c);
    }

    // if there is no check-sat, then the sat/unsat result of the query is not produced
    if !check_sat_found {
        return Err(ReconstructErr::CheckSatNotFound);
    }

    Ok(commands
        .iter()
        .map(|o| o.to_string())
        .collect::<Vec<String>>()
        .join("\n"))
}

/// function that, given the name of an SMTLIB query, will attempt to
/// read in the mapping file and result of running the transpiled query
/// and produce a result that indicates the result of the reconstruction
///
/// if the transpiled query produced anything other than SAT with a model built, then
/// the reconstruction will return this result. otherwise, it'll create a new SMLTIB file
/// that is the original query with assertions of the constraint variables equal to the
/// unmapped solution strings
pub fn reconstruct_and_add_assertions(
    path: String,
    ext: String,
) -> Result<ReconstructResult, ReconstructErr> {
    let new_map = mapping_tools::Mapping::build_from_json_file(&(path.clone() + "_mapping.json"));
    if let Err(_e) = new_map {
        return Err(ReconstructErr::MappingFileReadError);
    }
    let new_map = new_map.unwrap();

    let transformed_file = fs::File::open(path.clone() + "_transformed.out");
    if transformed_file.is_err() {
        return Err(ReconstructErr::TransformOutputFileReadError);
    }
    let transformed_file = transformed_file.unwrap();

    let mut transformed_reader = io::BufReader::new(transformed_file);
    let mut line = String::new();
    if transformed_reader.read_line(&mut line).is_err() {
        return Err(ReconstructErr::TransformOutputFileReadError);
    }
    // if it's anything other than SAT with model, return the result
    match line.as_str() {
        "unsat\n" => {
            return Ok(ReconstructResult::Unsat);
        }
        "timeout\n" => {
            return Ok(ReconstructResult::Timeout);
        }
        "unknown\n" => {
            return Ok(ReconstructResult::Unknown);
        }
        "sat\n" => {
            // skip the next line since it's a pointless paren that breaks the parse
            // if there is an error this means there is no next line, so bail with SAT: no model
            let read_res = transformed_reader.read_line(&mut line);
            if line == "sat\n" || matches!(read_res, Err(_)) {
                return Ok(ReconstructResult::SatNoModel);
            }

            // else, keep going
        }
        _ => {
            println!("{:?}", line);
            return Err(ReconstructErr::UnexpectedTransformedModelParse);
        }
    }

    let model_out = CommandStream::new(transformed_reader, SyntaxBuilder, None);

    let mut new_assertions: Vec<Command> = Vec::new();

    for o in model_out.flatten() {
        if let Ok(comm) = amzn_smt_ir::convert::convert_command(o) {
            if let Some(new_assert) = build_string_var_assertions(&new_map, &comm) {
                new_assertions.push(new_assert);
            }
        }
    }

    // read in the original problem and add asserts
    let output_string = add_asserts_to_original_problem(path.clone(), ext.clone(), new_assertions)?;

    std::fs::write(path + "_recon_check." + &ext, output_string)
        .expect("Error in printing to file");

    Ok(ReconstructResult::SatModelBuilt)
}

/// function to reverse the mapping of a string (this only makes sense if the mapping is char-to-char)
/// if a char is not in the char_map this is not an error, the char will be unchanged
pub fn reconstruct_string(reconstruct_me: Vec<char>, re_map: HashMap<char, char>) -> String {
    reconstruct_me
        .iter()
        .map(|c| {
            if let Some(new_c) = re_map.get(c) {
                *new_c
            } else {
                *c
            }
        })
        .collect::<String>()
}

/// given a (define-fun) command that declares a var to be equal to a string constant,
/// this function creates a new assertion that the unmapped variable should be equal to the unmapped string constant
/// use case: given the output SAT model of a transpiled query, this function builds an assertion that
/// the unmapped variable maps to a value thats part of a satisfying solution for the original problem
/// if the command is not a define-fun of a mapped var, then the function just returns None
pub fn build_string_var_assertions(
    new_map: &mapping_tools::Mapping,
    command: &Command,
) -> Option<Command> {
    if let Command::DefineFun {
        sig: FunctionDec { name: var_name, .. },
        term: Term::Constant(c),
    } = command
    {
        let const_str = match c.as_ref() {
            Constant::String(s) => s,
            _ => return None,
        };
        let var_name_str = &var_name.0;
        if new_map.affected_constraint_vars.contains(var_name_str) {
            let reconstructed = reconstruct_string(
                const_str.chars().collect::<Vec<char>>(),
                new_map.get_re_map(),
            );

            // the solver doesn't play well with '\u{0}', it seems to be represented as \x00 so just
            // replace it with this
            let reconstructed = reconstructed.replace('\u{0}', "\\x00");

            let un_alpha_map = new_map.get_un_alpha_map();
            let var_name = match un_alpha_map.get(var_name_str) {
                Some(un_alpha_name) => ISymbol::from(un_alpha_name.as_str()),
                _ => var_name.clone(),
            };

            let new_assert = crate::transpiler_visitors::new_assert_equal(
                var_name,
                &Term::Constant(Constant::String(reconstructed).into()),
            );
            return Some(new_assert);
        }
    }
    None
}
