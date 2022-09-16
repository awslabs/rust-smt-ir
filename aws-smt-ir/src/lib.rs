//! Intermediate representation for SMT-LIB formulas.

#![warn(rustdoc::broken_intra_doc_links)]
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use itertools::Itertools;
pub use smallvec::smallvec as args;
use smallvec::SmallVec;
use smt2parser::{concrete::Command as Smt2ParserCommand, concrete::SyntaxBuilder, CommandStream};
use std::{convert::Infallible, io};

// This renaming is necessary for the derive macros to work in doctests/integration tests, since
// `proc_macro_crate` can't distinguish between those contexts (treated as separate crates) and
// normal code/tests inside the crate.
extern crate self as aws_smt_ir;

pub mod ackermann;
pub mod cnf;
pub mod eliminate;
pub mod fold;
pub mod term;
pub use term::*;
pub mod logic;
pub use logic::Logic;
mod script;
pub use script::*;
pub mod types;
pub use types::*;
pub mod model;
pub mod visit;

/// An uninhabited type, useful for defining theories that contain no operations beyond those in
/// SMT-LIB's Core theory.
pub type Void = std::convert::Infallible;

/// Parses an SMT-LIB file, returning an iterator of parsed SMT-LIB commands.
pub fn parse_commands(
    smtlib: impl io::BufRead,
) -> impl Iterator<Item = Result<Smt2ParserCommand, smt2parser::Error>> {
    CommandStream::new(smtlib, SyntaxBuilder, None)
}

/// Applies a fallible function to each distinct pair of arguments in `args`, corresponding to the
/// `:pairwise` SMT-LIB attribute.
pub fn try_pairwise<L: Logic, E>(
    args: &[Term<L>],
    mut each: impl FnMut(Term<L>, Term<L>) -> Result<Term<L>, E>,
) -> Result<Term<L>, E> {
    let args = args
        .iter()
        .tuple_combinations()
        .map(|(l, r)| each(l.clone(), r.clone()))
        .collect::<Result<_, _>>()?;
    Ok(CoreOp::And(args).into())
}

/// Applies `each` to each distinct pair of arguments in `args`, corresponding to the `:pairwise`
/// SMT-LIB attribute.
pub fn pairwise<L: Logic>(
    args: &[Term<L>],
    mut each: impl FnMut(Term<L>, Term<L>) -> Term<L>,
) -> Term<L> {
    match try_pairwise(args, |x, y| Ok::<_, Infallible>(each(x, y))) {
        Ok(res) => res,
        Err(e) => match e {},
    }
}

/// Applies a fallible function to each adjacent pair of arguments in `args`, corresponding to the
/// `:chainable` SMT-LIB attribute.
pub fn try_chained<L: Logic, E>(
    args: impl IntoIterator<Item = Term<L>>,
    mut each: impl FnMut(Term<L>, Term<L>) -> Result<Term<L>, E>,
) -> Result<Term<L>, E> {
    let mut args: SmallVec<_> = args
        .into_iter()
        .tuple_windows()
        .map(|(l, r)| each(l, r))
        .collect::<Result<_, _>>()?;
    if args.len() == 1 {
        Ok(args.remove(0))
    } else {
        Ok(CoreOp::And(args).into())
    }
}

/// Applies `each` to each adjacent pair of arguments in `args`, corresponding to the `:chainable`
/// SMT-LIB attribute.
pub fn chained<L: Logic>(
    args: impl IntoIterator<Item = Term<L>>,
    mut each: impl FnMut(Term<L>, Term<L>) -> Term<L>,
) -> Term<L> {
    match try_chained(args, |x, y| Ok::<_, Infallible>(each(x, y))) {
        Ok(res) => res,
        Err(e) => match e {},
    }
}
