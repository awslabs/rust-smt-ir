// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    fold::Fold, visit::Visit, Ctx, IIndex, IOp, ISort, Logic, Operation, QualIdentifier, Sorted,
    Term, UnknownSort, Void, UF,
};
use smallvec::SmallVec;

type Args<T> = SmallVec<[T; 2]>;

#[derive(Operation, Fold, Visit, Clone, Hash, PartialEq, Eq)]
pub enum LIAOp<Term> {
    #[symbol("+")]
    Plus(Args<Term>),
    #[symbol("-")]
    Neg(Term),
    #[symbol("-")]
    Minus(Args<Term>),
    #[symbol("*")]
    Mul(Args<Term>),
    #[symbol(">=")]
    Gte(Args<Term>),
    #[symbol(">")]
    Gt(Args<Term>),
    #[symbol("<=")]
    Lte(Args<Term>),
    #[symbol("<")]
    Lt(Args<Term>),
}

impl<L: Logic> Sorted<L> for LIAOp<Term<L>> {
    fn sort(&self, _: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        match self {
            Self::Plus(..) | Self::Neg(..) | Self::Minus(..) | Self::Mul(..) => Ok(ISort::int()),
            Self::Gte(..) | Self::Gt(..) | Self::Lte(..) | Self::Lt(..) => Ok(ISort::bool()),
        }
    }
}

#[derive(Operation, Fold, Visit, Clone, Hash, PartialEq, Eq)]
pub enum ArithOp<Term> {
    #[symbol("+")]
    Plus(Args<Term>),
    #[symbol("-")]
    Neg(Term),
    #[symbol("-")]
    Minus(Args<Term>),
    #[symbol("*")]
    Mul(Args<Term>),
    #[symbol("div")]
    IntDiv(Args<Term>),
    #[symbol("/")]
    RealDiv(Args<Term>),
    Divisible([IIndex; 1], Term),
    Mod(Term, Term),
    Abs(Term),
    #[symbol(">=")]
    Gte(Args<Term>),
    #[symbol(">")]
    Gt(Args<Term>),
    #[symbol("<=")]
    Lte(Args<Term>),
    #[symbol("<")]
    Lt(Args<Term>),
    #[symbol("to_real")]
    ToReal(Term),
    #[symbol("to_int")]
    ToInt(Term),
    #[symbol("is_int")]
    IsInt(Term),
}

impl<L: Logic> Sorted<L> for ArithOp<Term<L>>
where
    Self: Into<L::Op>,
{
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        use ArithOp::*;

        let bad = || UnknownSort(Term::from(IOp::new(self.clone().into())));
        match self {
            Neg(arg) => arg.sort(ctx),
            Plus(args) | Minus(args) | Mul(args) => args.first().ok_or_else(bad)?.sort(ctx),
            IntDiv(..) | Mod(..) | Abs(..) | ToInt(..) => Ok(ISort::int()),
            RealDiv(..) | ToReal(..) => Ok(ISort::real()),
            Gte(..) | Gt(..) | Lte(..) | Lt(..) | Divisible(..) | IsInt(..) => Ok(ISort::bool()),
        }
    }
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub struct QF_UFLIA;

impl Logic for QF_UFLIA {
    type Var = QualIdentifier;
    type Op = LIAOp<Term<Self>>;
    type Quantifier = Void;
    type UninterpretedFunc = UF<Term<Self>>;
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub struct QF_LIA;

impl Logic for QF_LIA {
    type Var = QualIdentifier;
    type Op = LIAOp<Term<Self>>;
    type Quantifier = Void;
    type UninterpretedFunc = Void;
}
