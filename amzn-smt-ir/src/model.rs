// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{Command, FunctionDec, ISort, ISymbol, Logic, Script, Term};
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

    pub fn from_script(script: Script<Term<L>>) -> Result<Self, Box<dyn std::error::Error>> {
        let elems_result: Result<Vec<DefineFun<Term<L>>>, Box<dyn std::error::Error>> = script
            .into_iter()
            .map(|elem| match elem {
                Command::DefineFun { sig, term } => Ok(DefineFun {
                    sym: sig.name,
                    args: sig.parameters,
                    sort: sig.result,
                    body: term,
                }),
                _ => Err(format!("Script element {} cannot be converted to a Model", &elem).into()),
            })
            .collect();

        Ok(Self {
            defns: elems_result?,
        })
    }

    pub fn into_script(self) -> Script<Term<L>> {
        let iter = self.defns.into_iter().map(|elem| {
            let sig: FunctionDec = FunctionDec {
                name: elem.sym,
                parameters: elem.args,
                result: elem.sort,
            };

            Command::DefineFun {
                sig,
                term: elem.body,
            }
        });
        Script::from_iter(iter)
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
