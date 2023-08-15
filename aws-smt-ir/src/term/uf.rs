//! Uninterpreted function abstraction.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::operation::InvalidOp;
use crate::{ISymbol, Internable, Logic, QualIdentifier, Sorted, Term, Void, IUF};
use std::fmt;

/// An `UninterpretedFunction` can be used to represent uninterpreted functions.
pub trait UninterpretedFunction<T: Logic>: Sized + Sorted<T> {
    /// Parses an uninterpreted function from a symbol and list of arguments.
    fn parse(func: QualIdentifier, args: Vec<Term<T>>) -> Result<Self, InvalidOp<T>>;

    /// Produces the function.
    fn func(&self) -> QualIdentifier;

    /// Produces the function symbol
    fn func_symbol(&self) -> ISymbol;
}

/// An uninterpreted function applied to some arguments
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct UF<Term> {
    pub func: QualIdentifier,
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
    fn parse(func: QualIdentifier, args: Vec<Term<L>>) -> Result<Self, InvalidOp<L>> {
        L::UninterpretedFunc::parse(func, args).map(Into::into)
    }

    fn func(&self) -> QualIdentifier {
        self.as_ref().func()
    }

    fn func_symbol(&self) -> ISymbol {
        self.as_ref().func_symbol()
    }
}

impl<L: Logic<Var = QualIdentifier>> UninterpretedFunction<L> for UF<Term<L>> {
    fn parse(func: QualIdentifier, args: Vec<Term<L>>) -> Result<Self, InvalidOp<L>> {
        let args = args.into_boxed_slice();
        Ok(Self { func, args })
    }

    fn func(&self) -> QualIdentifier {
        self.func.clone()
    }

    fn func_symbol(&self) -> ISymbol {
        self.func().sym().clone()
    }
}

impl<L: Logic<UninterpretedFunc = UF<T>>, T: Internable> From<UF<T>> for Term<L> {
    fn from(uf: UF<T>) -> Self {
        Self::UF(uf.into())
    }
}

impl<T: Logic> UninterpretedFunction<T> for Void {
    fn parse(func: QualIdentifier, args: Vec<Term<T>>) -> Result<Self, InvalidOp<T>> {
        Err(InvalidOp { func, args })
    }

    fn func(&self) -> QualIdentifier {
        match *self {}
    }

    fn func_symbol(&self) -> ISymbol {
        match *self {}
    }
}

impl<L: Logic> From<Void> for IUF<L> {
    fn from(x: Void) -> Self {
        match x {}
    }
}
