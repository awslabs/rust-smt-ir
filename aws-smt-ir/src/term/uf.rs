//! Uninterpreted function abstraction.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::operation::InvalidOp;
use crate::{ISymbol, Internable, Logic, QualIdentifier, Sorted, Term, Void, IUF};
use std::fmt;

/// An `UninterpretedFunction` can be used to represent uninterpreted functions.
pub trait UninterpretedFunction<T: Logic>: Sized + Sorted<T> {
    /// Parses an uninterpreted function from a symbol and list of arguments.
    fn parse(func: ISymbol, args: Vec<Term<T>>) -> Result<Self, InvalidOp<T>>;

    /// Produces the function symbol of the function application.
    fn func(&self) -> ISymbol;
}

/// An uninterpreted function applied to some arguments
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct UF<Term> {
    pub func: ISymbol,
    pub args: Box<[Term]>,
}

impl<Term: fmt::Display> fmt::Display for UF<Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}", self.func)?;
        for arg in self.args.iter() {
            write!(f, " {}", arg)?;
        }
        write!(f, ")")
    }
}

impl<L: Logic> UninterpretedFunction<L> for IUF<L> {
    fn parse(func: ISymbol, args: Vec<Term<L>>) -> Result<Self, InvalidOp<L>> {
        L::UninterpretedFunc::parse(func, args).map(Into::into)
    }

    fn func(&self) -> ISymbol {
        self.as_ref().func()
    }
}

impl<L: Logic<Var = QualIdentifier>> UninterpretedFunction<L> for UF<Term<L>> {
    fn parse(func: ISymbol, args: Vec<Term<L>>) -> Result<Self, InvalidOp<L>> {
        let args = args.into_boxed_slice();
        Ok(Self { func, args })
    }

    fn func(&self) -> ISymbol {
        self.func.clone()
    }
}

impl<L: Logic<UninterpretedFunc = UF<T>>, T: Internable> From<UF<T>> for Term<L> {
    fn from(uf: UF<T>) -> Self {
        Self::UF(uf.into())
    }
}

impl<T: Logic> UninterpretedFunction<T> for Void {
    fn parse(func: ISymbol, args: Vec<Term<T>>) -> Result<Self, InvalidOp<T>> {
        let func = func.into();
        Err(InvalidOp { func, args })
    }

    fn func(&self) -> ISymbol {
        match *self {}
    }
}

impl<L: Logic> From<Void> for IUF<L> {
    fn from(x: Void) -> Self {
        match x {}
    }
}
