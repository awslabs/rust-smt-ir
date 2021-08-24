//! Quantifier abstraction.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{IQuantifier, ISort, ISymbol, Logic, Term, Void};
use std::fmt;

/// A `Quantifier` can be used to represent quantifiers.
pub trait Quantifier<T: Logic>: Sized {
    /// Parses a quantifier from a set of bindings and a term.
    fn parse(
        kind: Kind,
        bindings: Vec<(ISymbol, ISort)>,
        term: Term<T>,
    ) -> Result<Self, InvalidQuantifier<T>>;
}

/// Kinds of quantifiers.
#[derive(Debug, Hash, PartialEq, Eq)]
pub enum Kind {
    Universal,
    Existential,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct InvalidQuantifier<T: Logic>(crate::Quantifier<Term<T>>);

impl<T: Logic> fmt::Display for InvalidQuantifier<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Invalid quantifier in logic {:?}: {}",
            T::default(),
            self.0
        )
    }
}

impl<T: Logic> std::error::Error for InvalidQuantifier<T> {}

impl<T: Logic> Quantifier<T> for Void {
    fn parse(
        kind: Kind,
        bindings: Vec<(ISymbol, ISort)>,
        term: Term<T>,
    ) -> Result<Self, InvalidQuantifier<T>> {
        Err(InvalidQuantifier(crate::Quantifier::new(
            kind, bindings, term,
        )))
    }
}

impl<L: Logic> From<Void> for IQuantifier<L> {
    fn from(x: Void) -> Self {
        match x {}
    }
}
