//! Intermediate representation for SMT-LIB terms.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    logic::ALL, Constant, IConst, ICoreOp, ILet, IMatch, IOp, IQuantifier, ISymbol, Internable,
    Logic, QualIdentifier, Void, IUF,
};
use internment::Intern;
use num_traits::Zero;
use smallvec::SmallVec;
use std::{hash::Hash, iter, ops};

pub mod args;
pub use args::Arguments;
use args::Iterate;
mod binder;
pub use binder::{Let, Match, Quantifier};
pub mod convert;
mod fmt;
mod operation;
pub use operation::{InvalidOp, Operation};
pub mod quantifier;
mod sort_checking;
pub use sort_checking::*;
mod substitute;
pub mod uf;
use uf::UninterpretedFunction;
pub use uf::UF;

/// `Term<T: Logic>` represents an SMT term in the logic `T`.
///
/// See [`Logic`] for examples of defining theories.
///
/// # Examples
///
/// ## Boolean terms
///
/// ```
/// # fn main() {
/// use amzn_smt_ir::{CoreOp, Term, Void};
/// use smt2parser::concrete::Constant;
///
/// let constant: Term = Term::Constant(Constant::Numeral(0u8.into()).into());
/// let variable = Term::Variable("x".into());
/// // true => x
/// let _implies = Term::CoreOp(CoreOp::Imp([constant, variable].into()).into());
/// # }
/// ```
///
/// ## [`std::ops`] operators
///
/// [`Term`] implements [`ops::Not`], [`ops::BitAnd`], [`ops::BitOr`], and [`ops::BitXor`] to
/// succinctly construct the common patterns `(not x)`, `(and x y)`, `(or x y)`, and `(xor x y`):
///
/// ```
/// # fn main() {
/// # use amzn_smt_ir::{CoreOp, Term, Void, IVar};
/// use Term::*;
///
/// let (x, y): (IVar, IVar) = ("x".into(), "y".into());
/// let _not: Term = !Variable(x.clone());
/// let _and: Term = Variable(x.clone()) & Variable(y.clone());
/// let _or: Term = Variable(x.clone()) | Variable(y.clone());
/// let _xor: Term = Variable(x) ^ Variable(y);
/// # }
/// ```
#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Term<T: Logic = ALL> {
    /// A constant value.
    Constant(IConst),

    /// A variable representing a value.
    Variable(IVar<T::Var>),

    /// An operation in SMT-LIB's Core theory.
    CoreOp(ICoreOp<T>),

    /// A non-Core operation.
    OtherOp(IOp<T>),

    /// An uninterpreted function.
    UF(IUF<T>),

    /// Simultaneous let-binding e.g. `(let ((x true) (y false)) (and x y))`
    Let(ILet<T>),

    /// SMT-LIB `match` expression -- not yet supported
    Match(IMatch<T>),

    /// Quantified term.
    Quantifier(IQuantifier<T>),
}

#[cfg(test)]
static_assertions::assert_eq_size!(Term<crate::logic::ALL>, [*const (); 2]);

impl<T: Logic> Term<T> {
    /// Determines if a term is the numeral constant `0`.
    pub fn is_zero(&self) -> bool {
        match self {
            Self::Constant(c) => match c.as_ref() {
                Constant::Numeral(n) => n.is_zero(),
                _ => false,
            },
            _ => false,
        }
    }

    /// Produces the boolean constant corresponding to a term, if the term is `true`, `false`, or
    /// a negation of either.
    pub fn const_bool(&self) -> Result<bool, &Self> {
        match self {
            Self::CoreOp(op) => match op.as_ref() {
                CoreOp::True => Ok(true),
                CoreOp::False => Ok(false),
                CoreOp::Not(t) => match t.const_bool() {
                    Ok(x) => Ok(!x),
                    Err(_) => Err(self),
                },
                _ => Err(self),
            },
            _ => Err(self),
        }
    }

    // FIXME: does this make more sense or does it make more sense to group the three into a
    // variant of the actual Term enum?
    pub fn op(&self) -> Option<OpRef<T>> {
        match self {
            Self::CoreOp(op) => Some(OpRef::Core(op)),
            Self::OtherOp(op) => Some(OpRef::Other(op)),
            Self::UF(op) => Some(OpRef::Uninterpreted(op)),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum OpRef<'a, L: Logic> {
    Core(&'a ICoreOp<L>),
    Other(&'a IOp<L>),
    Uninterpreted(&'a IUF<L>),
}

impl<'a, L: Logic> OpRef<'a, L> {
    pub fn func(&self) -> ISymbol {
        match self {
            Self::Core(op) => op.func(),
            Self::Other(op) => op.func(),
            Self::Uninterpreted(op) => op.func(),
        }
    }
}

impl<'a, L: Logic> Iterate<'a, L> for OpRef<'a, L> {
    type Terms = Box<dyn Iterator<Item = &'a Term<L>> + 'a>;
    type IntoTerms = iter::Cloned<Self::Terms>;

    fn terms(&'a self) -> Self::Terms {
        match self {
            Self::Core(op) => op.terms(),
            Self::Other(op) => Box::new(op.terms()),
            Self::Uninterpreted(op) => Box::new(op.terms()),
        }
    }

    fn into_terms(self) -> Self::IntoTerms {
        let iter = match self {
            Self::Core(op) => op.terms(),
            Self::Other(op) => Box::new(op.terms()),
            Self::Uninterpreted(op) => Box::new(op.terms()),
        };
        iter.cloned()
    }
}

impl<'a, L: Logic> Arguments<'a, L> for OpRef<'a, L> {}

/// An SMT variable e.g. `Var<String>` if variables are represented by strings.
#[derive(Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct IVar<T: Internable = QualIdentifier>(Intern<T>);

impl From<ISymbol> for IVar<QualIdentifier> {
    fn from(sym: ISymbol) -> Self {
        Self::from(QualIdentifier::from(sym))
    }
}

impl From<&ISymbol> for IVar<QualIdentifier> {
    fn from(sym: &ISymbol) -> Self {
        Self::from(QualIdentifier::from(sym.clone()))
    }
}

impl From<&str> for IVar<QualIdentifier> {
    fn from(sym: &str) -> Self {
        Self::from(QualIdentifier::from(sym))
    }
}

impl<T: Internable> From<T> for IVar<T> {
    fn from(v: T) -> Self {
        IVar(v.into())
    }
}

impl<T: Internable> From<&T> for IVar<T>
where
    for<'a> T: From<&'a T>,
{
    fn from(v: &T) -> Self {
        IVar(Intern::from_ref(v))
    }
}

impl<T: Internable> Clone for IVar<T> {
    fn clone(&self) -> Self {
        // TODO: this is Copy now, but once `Intern` is switched to `ArcIntern`
        // it will no longer be.
        #[allow(clippy::clone_on_copy)]
        Self(self.0.clone())
    }
}

impl<T: Internable> ops::Deref for IVar<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Internable> AsRef<T> for IVar<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

type Args<T> = SmallVec<[T; 2]>;

/// An SMT-LIB Core operation containing subterms of type `Term`.
#[derive(Clone, Operation, Hash, PartialEq, Eq)]
#[core_op]
pub enum CoreOp<Term> {
    /// True i.e. `true`.
    True,

    /// False i.e. `false`.
    False,

    /// Logical negation e.g. `(not x)`.
    Not(Term),

    /// Conjunction e.g. `(and x y ...)`.
    And(Args<Term>),

    /// Disjunction e.g. `(or x y ...)`.
    Or(Args<Term>),

    /// Exclusive disjunction e.g. `(xor x y ...)`.
    Xor(Args<Term>),

    /// Implication e.g. `(=> x y)`.
    #[symbol("=>")]
    Imp(Args<Term>),

    /// Equality/bi-implication e.g. `(= x y)`.
    #[symbol("=")]
    Eq(Args<Term>),

    /// Determines whether a set of terms are distinct e.g. `(distinct x y)`.
    Distinct(Args<Term>),

    /// If-then-else e.g. `(ite cond consq alt)` (if `cond` then `consq` else `alt`).
    Ite(Term, Term, Term),
}

#[cfg(test)]
static_assertions::assert_eq_size!(CoreOp<Term<crate::logic::ALL>>, [*const (); 7]);

impl<Term> From<bool> for CoreOp<Term> {
    fn from(b: bool) -> Self {
        if b {
            Self::True
        } else {
            Self::False
        }
    }
}

impl<L: Logic> From<bool> for ICoreOp<L> {
    fn from(b: bool) -> Self {
        CoreOp::from(b).into()
    }
}

impl<L: Logic> From<bool> for Term<L> {
    fn from(b: bool) -> Self {
        ICoreOp::from(b).into()
    }
}

impl<T: Logic> ops::Not for Term<T> {
    type Output = Self;
    fn not(self) -> Self::Output {
        Self::CoreOp(CoreOp::Not(self).into())
    }
}

impl<T: Logic> ops::BitAnd for Term<T> {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        Self::CoreOp(CoreOp::And([self, rhs].into()).into())
    }
}

impl<T: Logic> ops::BitOr for Term<T> {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self::CoreOp(CoreOp::Or([self, rhs].into()).into())
    }
}

impl<T: Logic> ops::BitXor for Term<T> {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self::Output {
        Self::CoreOp(CoreOp::Xor([self, rhs].into()).into())
    }
}

impl<T: Logic> From<ICoreOp<T>> for Term<T> {
    fn from(op: ICoreOp<T>) -> Self {
        Term::CoreOp(op)
    }
}

impl<T: Logic> From<CoreOp<Term<T>>> for Term<T> {
    fn from(op: CoreOp<Term<T>>) -> Self {
        ICoreOp::from(op).into()
    }
}

impl<T: Logic> From<IOp<T>> for Term<T> {
    fn from(op: IOp<T>) -> Self {
        Term::OtherOp(op)
    }
}

impl<T: Logic> From<IUF<T>> for Term<T> {
    fn from(op: IUF<T>) -> Self {
        Term::UF(op)
    }
}

impl<T: Logic> From<ILet<T>> for Term<T> {
    fn from(l: ILet<T>) -> Self {
        Term::Let(l)
    }
}

impl<T: Logic> From<IMatch<T>> for Term<T> {
    fn from(m: IMatch<T>) -> Self {
        Term::Match(m)
    }
}

impl<T: Logic> From<IQuantifier<T>> for Term<T> {
    fn from(q: IQuantifier<T>) -> Self {
        Term::Quantifier(q)
    }
}

impl<T: Logic> From<Void> for Term<T> {
    fn from(v: Void) -> Self {
        match v {}
    }
}

#[cfg(test)]
mod tests {
    use super::{sort_checking::UnknownSort, *};
    use crate::{
        args::Arguments,
        fold::{Fold, IntraLogicFolder, SuperFold},
        logic::ALL,
        visit::{SuperVisit, Visit, Visitor},
        IIndex, ISort, Index, ParseError, QualIdentifier, Quantifier, Void,
    };
    use std::{
        convert::Infallible,
        fmt::{Debug, Display},
        str::FromStr,
    };

    // This is a roundabout way to parse a term, but smt2parser doesn't expose functionality for
    // parsing anything but commands. Restrict to tests until it can be made more efficient.
    #[cfg(test)]
    impl<L: Logic> FromStr for Term<L>
    where
        QualIdentifier: Into<L::Var>,
    {
        type Err = ParseError<L>;

        fn from_str(smt: &str) -> Result<Self, Self::Err> {
            let smt = format!("(assert {})", smt);
            let script = crate::Script::<Term<L>>::parse(smt.as_bytes())?;
            Ok(script.into_asserted_terms().next().unwrap())
        }
    }

    #[test]
    fn rendering() {
        let c = Term::<ALL>::CoreOp(CoreOp::from(true).into());
        assert_eq!((!c.clone()).to_string(), "(not true)");
        assert_eq!((c.clone() & !c).to_string(), "(and true (not true))");
    }

    #[test]
    fn parse_true_false() {
        let parse = |smt| Term::<ALL>::from_str(smt).unwrap();
        assert_eq!(parse("true"), CoreOp::True.into());
        assert_eq!(parse("false"), CoreOp::False.into());
    }

    #[test]
    fn iterate_core_op() {
        type T = ALL;
        fn args_eq<'a>(x: &'a impl Arguments<'a, T>, y: impl IntoIterator<Item = &'a Term<T>>) {
            assert_eq!(
                x.args().collect::<Vec<_>>(),
                y.into_iter().collect::<Vec<_>>()
            );
        }
        let (x, y, z): (Term<T>, Term<T>, Term<T>) = (true.into(), false.into(), false.into());
        let not = CoreOp::Not(x.clone());
        args_eq(&not, [&x]);
        let and = CoreOp::And([x.clone(), y.clone()].into());
        args_eq(&and, [&x, &y]);
        let ite = CoreOp::Ite(x.clone(), y.clone(), z.clone());
        args_eq(&ite, [&x, &y, &z]);
    }

    #[derive(Clone, Operation, Visit, Fold, Hash, PartialEq, Eq)]
    enum Op<Term> {
        #[symbol("-")]
        Negative(Term),
        #[symbol("-")]
        Minus(Term, Term),
        #[symbol("+")]
        Plus(Vec<Term>),
        #[symbol("foo")]
        Indexed([IIndex; 2], Term),
    }

    impl<L: Logic> Sorted<L> for Op<Term<L>> {
        fn sort(&self, _: &mut crate::Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
            Ok(ISort::int())
        }
    }

    macro_rules! assert_impl_standard_traits {
        ($($t:ty),*) => {
            $(assert_impl_all!($t: Clone, Debug, Display, Hash, PartialEq, Eq);)*
        };
    }

    macro_rules! check {
        ($T: ty) => {
            use super::{
                Debug, Display, Fold, Hash, ICoreOp, IOp, Infallible, IntraLogicFolder, Let, Logic,
                Match, Operation, SuperFold, SuperVisit, Visit, Visitor,
            };
            use static_assertions::assert_impl_all;

            type F = super::Term<$T>;
            type CoreOp = super::CoreOp<F>;
            type TheoryOp = <$T as Logic>::Op;
            #[allow(dead_code)]
            type Quantifier = <$T as Logic>::Quantifier;

            assert_impl_standard_traits!(CoreOp, TheoryOp, Let<F>, Match<F>, Quantifier, F);
            assert_impl_all!(CoreOp: Operation<$T>);
            assert_impl_all!(TheoryOp: Operation<$T>);

            struct X;

            impl IntraLogicFolder<$T> for X {
                type Error = Infallible;
            }

            impl Visitor<$T> for X {
                type BreakTy = ();
            }

            #[allow(dead_code, path_statements)]
            fn fold_impls() {
                <ICoreOp<$T> as Fold<$T, F>>::fold_with::<X, _>;
                <IOp<$T> as Fold<$T, F>>::fold_with::<X, _>;
                <F as Fold<$T, F>>::fold_with::<X, _>;
            }

            #[allow(dead_code, path_statements)]
            fn super_fold_impls() {
                <CoreOp as SuperFold<$T, F>>::super_fold_with::<X, _>;
                <TheoryOp as SuperFold<$T, F>>::super_fold_with::<X, _>;
                <F as SuperFold<$T, F>>::super_fold_with::<X, _>;
            }

            #[allow(dead_code, path_statements)]
            fn visit_impls() {
                <ICoreOp<$T> as Visit<$T>>::visit_with::<X>;
                <IOp<$T> as Visit<$T>>::visit_with::<X>;
                <F as Visit<$T>>::visit_with::<X>;
            }

            #[allow(dead_code, path_statements)]
            fn super_visit_impls() {
                <CoreOp as SuperVisit<$T>>::super_visit_with::<X>;
                <TheoryOp as SuperVisit<$T>>::super_visit_with::<X>;
                <F as SuperVisit<$T>>::super_visit_with::<X>;
            }
        };
    }

    #[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
    struct QF;
    impl Logic for QF {
        type Var = QualIdentifier;
        type Op = Op<Term<Self>>;
        type Quantifier = Void;
        type UninterpretedFunc = Void;
    }
    mod check_qf {
        check!(super::QF);
    }

    #[test]
    fn parse_indexed_fun() {
        let test_roundtrip = |smt: &str, expected: Term<QF>| {
            let actual = Term::<QF>::from_str(smt).unwrap();
            assert_eq!(expected, actual);
            assert_eq!(actual.to_string(), smt);
        };
        test_roundtrip(
            "((_ foo 1 2) 3)",
            Op::Indexed(
                [
                    Index::Numeral(1u8.into()).into(),
                    Index::Numeral(2u8.into()).into(),
                ],
                Term::Constant(Constant::Numeral(3u8.into()).into()),
            )
            .into(),
        );
    }

    #[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
    struct Q;
    impl Logic for Q {
        type Var = QualIdentifier;
        type Op = Op<Term<Self>>;
        type Quantifier = Quantifier<Term<Self>>;
        type UninterpretedFunc = Void;
    }
    mod check_with_quantifiers {
        check!(super::Q);
    }

    #[allow(clippy::upper_case_acronyms)]
    #[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
    struct QUF;
    impl Logic for QUF {
        type Var = QualIdentifier;
        type Op = Op<Term<Self>>;
        type Quantifier = Quantifier<Term<Self>>;
        type UninterpretedFunc = UF<Term<Self>>;
    }
    mod check_with_quantifiers_and_uf {
        check!(super::QUF);
    }
}
