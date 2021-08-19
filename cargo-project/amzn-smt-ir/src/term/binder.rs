//! SMT-LIB binders: `let`, `match`, `forall`, and `exists`.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::{quantifier, Logic, Term};
use crate::{
    fold::{Fold, Folder, SuperFold},
    quantifier::InvalidQuantifier,
    IMatch, ISort, ISymbol, Internable,
};
use std::fmt;

/// Simultaneous let-binding e.g. `(let ((x true) (y false)) (and x y))
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Let<Term> {
    /// Variables bound by the let (simultaneously).
    pub bindings: Vec<(ISymbol, Term)>,
    /// Term with environment extended by the bindings.
    pub term: Term,
}

/// SMT-LIB `match` expression -- not yet supported
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Match<Term>(Term);

/// Standard SMT-LIB quantifiers: `forall` and `exists`.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Quantifier<Term> {
    /// Universal quantification.
    Forall(Vec<(ISymbol, ISort)>, Term),
    /// Existential quantification.
    Exists(Vec<(ISymbol, ISort)>, Term),
}

impl<Term> Quantifier<Term> {
    pub(crate) fn new(kind: quantifier::Kind, bindings: Vec<(ISymbol, ISort)>, term: Term) -> Self {
        match kind {
            quantifier::Kind::Universal => Self::Forall(bindings, term),
            quantifier::Kind::Existential => Self::Exists(bindings, term),
        }
    }
}

impl<T: Logic<Quantifier = Self>> quantifier::Quantifier<T> for Quantifier<Term<T>> {
    fn parse(
        kind: quantifier::Kind,
        bindings: Vec<(ISymbol, ISort)>,
        term: Term<T>,
    ) -> Result<Self, InvalidQuantifier<T>> {
        Ok(Self::new(kind, bindings, term))
    }
}

impl<T: Logic, Out> Fold<T, Out> for IMatch<T> {
    type Output = Out;

    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        folder.fold_match(self)
    }
}

impl<T: Logic, Out, Inner> SuperFold<T, Out> for Match<Inner>
where
    Inner: Fold<T, Out>,
{
    type Output = Match<Inner::Output>;

    fn super_fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        self.0.fold_with(folder).map(Match)
    }
}

impl<Term: fmt::Display> fmt::Display for Let<Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { bindings, term } = self;
        write!(f, "(let (")?;
        let mut bindings = bindings.iter();
        if let Some((var, t)) = bindings.next() {
            write!(f, "({} {})", var, t)?;
        }
        for (var, t) in bindings {
            write!(f, " ({} {})", var, t)?;
        }
        write!(f, ") {})", term)
    }
}

impl<Term: fmt::Display> fmt::Display for Match<Term> {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!("match is currently unsupported")
    }
}

impl<Term: fmt::Display> fmt::Display for Quantifier<Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (kind, bindings, t) = match self {
            Self::Forall(bindings, t) => ("forall", bindings, t),
            Self::Exists(bindings, t) => ("exists", bindings, t),
        };
        write!(f, "({} (", kind)?;
        let mut bindings = bindings.iter();
        if let Some((var, sort)) = bindings.next() {
            write!(f, "({} {})", var, sort)?;
        }
        for (var, sort) in bindings {
            write!(f, " ({} {})", var, sort)?;
        }
        write!(f, ") {})", t)
    }
}

impl<T: Logic> From<Let<Term<T>>> for Term<T> {
    fn from(l: Let<Term<T>>) -> Self {
        Self::Let(l.into())
    }
}

impl<T: Logic> From<Match<Self>> for Term<T> {
    fn from(m: Match<Self>) -> Self {
        Self::Match(m.into())
    }
}

impl<L: Logic<Quantifier = Quantifier<T>>, T: Internable> From<Quantifier<T>> for Term<L> {
    fn from(q: Quantifier<T>) -> Self {
        Self::Quantifier(q.into())
    }
}

#[test]
fn roundtrip() {
    use crate::{
        types::Numeral, Constant, CoreOp, IConst, ISymbol, IVar, Identifier, QualIdentifier,
        Symbol, Void,
    };
    use std::str::FromStr;

    #[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
    struct T;
    impl Logic for T {
        type Var = QualIdentifier;
        type Op = Void;
        type Quantifier = Quantifier<Term<Self>>;
        type UninterpretedFunc = Void;
    }

    let ident = |ident: &str| -> Term<T> {
        let ident = Identifier::<ISymbol>::Simple {
            symbol: Symbol(ident.to_string()).into(),
        };
        let qual = QualIdentifier::Simple {
            identifier: ident.into(),
        };
        Term::from(IVar::from(qual))
    };
    let val = |x: u8| Term::from(IConst::from(Constant::Numeral(Numeral::from(x))));
    let sym = |s: &str| ISymbol::from(Symbol(s.to_string()));
    let test_roundtrip = |smt: &str, expected| {
        let actual = Term::<T>::from_str(smt).unwrap();
        assert_eq!(expected, actual);
        assert_eq!(actual.to_string(), smt);
    };

    test_roundtrip(
        "(forall ((x Bool) (y Bool)) (and x y))",
        Term::Quantifier(
            Quantifier::Forall(
                vec![(sym("x"), ISort::bool()), (sym("y"), ISort::bool())],
                ident("x") & ident("y"),
            )
            .into(),
        ),
    );

    test_roundtrip(
        "(exists ((x Bool) (y Bool)) (and x y))",
        Term::Quantifier(
            Quantifier::Exists(
                vec![(sym("x"), ISort::bool()), (sym("y"), ISort::bool())],
                ident("x") & ident("y"),
            )
            .into(),
        ),
    );

    test_roundtrip(
        "(let ((x 1) (y 2)) (= x y))",
        Term::Let(
            Let {
                bindings: vec![(sym("x"), val(1)), (sym("y"), val(2))],
                term: CoreOp::Eq([ident("x"), ident("y")].into()).into(),
            }
            .into(),
        ),
    );
}
