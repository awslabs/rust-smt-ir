// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{ISort, ISymbol, Logic, Term};
use itertools::Itertools;
use std::{fmt, iter::FromIterator};

#[derive(Debug)]
pub struct DefineFun<Term> {
    pub sym: ISymbol,
    pub args: Vec<(ISymbol, ISort)>,
    pub sort: ISort,
    pub body: Term,
}

impl<Term> DefineFun<Term> {
    fn is_solver_internal(&self) -> bool {
        self.sym.is_solver_internal()
    }
}

#[derive(Debug)]
pub struct Model<L: Logic> {
    defns: Vec<DefineFun<Term<L>>>,
}

impl<L: Logic> FromIterator<DefineFun<Term<L>>> for Model<L> {
    fn from_iter<T: IntoIterator<Item = DefineFun<Term<L>>>>(iter: T) -> Self {
        Self {
            defns: iter.into_iter().collect(),
        }
    }
}

impl<L: Logic> Default for Model<L> {
    fn default() -> Self {
        Self::new()
    }
}

impl<L: Logic> Model<L> {
    pub fn new() -> Self {
        Self { defns: vec![] }
    }

    pub fn defns(&self) -> impl Iterator<Item = &DefineFun<Term<L>>> {
        self.defns.iter()
    }

    pub fn into_defns(self) -> impl Iterator<Item = DefineFun<Term<L>>> {
        self.defns.into_iter()
    }

    pub fn define_const(&mut self, sym: ISymbol, sort: ISort, val: Term<L>) {
        self.defns.push(DefineFun {
            sym,
            args: vec![],
            sort,
            body: val,
        });
    }

    pub fn get_const_value(&self, sym: &ISymbol) -> Option<Term<L>> {
        self.defns.iter().find_map(|x| match x {
            DefineFun {
                sym: s, args, body, ..
            } if s == sym && args.is_empty() => Some(body.clone()),
            _ => None,
        })
    }
}

impl<T: fmt::Display> fmt::Display for DefineFun<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(define-fun {} ({}) {} {})",
            self.sym,
            self.args
                .iter()
                .format_with(" ", |(sym, sort), f| f(&format_args!("({} {})", sym, sort))),
            self.sort,
            self.body
        )
    }
}

impl<L: Logic> fmt::Display for Model<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "(")?;
        for defn in self.defns.iter() {
            if !defn.is_solver_internal() {
                writeln!(f, "\t{}", defn)?;
            }
        }
        writeln!(f, ")")
    }
}
