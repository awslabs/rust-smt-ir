// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    fold::{Fold, Folder},
    Constant, CoreOp, Ctx, ICoreOp, IOp, IQuantifier, ISort, IVar, Identifier, Index, Logic,
    QualIdentifier, Quantifier, Term, Void, IUF, UF,
};
use std::fmt::{Debug, Display};

/// Defines sort-checking behavior for a type.
pub trait Sorted<L: Logic> {
    /// Determines the sort of `self`. If `self` is a variable, then its sort is the variable's
    /// sort; if `self` is a function application, then its sort is the function's return type.
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>>;
}

#[derive(Debug)]
pub struct SortChecker<'a>(&'a mut Ctx);

impl<L: Logic> Sorted<L> for Term<L> {
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        self.fold_with(&mut SortChecker(ctx))
    }
}

impl<L: Logic<Var = QualIdentifier>> Sorted<L> for UF<Term<L>> {
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        ctx.return_sort(&self.func).cloned().ok_or_else(|| {
            // TODO: this isn't really what it is, but it'll print out right
            UnknownSort(Term::from(IVar::from(QualIdentifier::from(
                self.func.clone(),
            ))))
        })
    }
}

impl<L: Logic> Sorted<L> for IUF<L> {
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        self.as_ref().sort(ctx)
    }
}

impl<L: Logic> Sorted<L> for Quantifier<Term<L>> {
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        match self {
            Self::Forall(_, term) | Self::Exists(_, term) => term.sort(ctx),
        }
    }
}

impl<L: Logic<Var = QualIdentifier>> Sorted<L> for QualIdentifier {
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        match self {
            Self::Simple { identifier } => {
                match identifier.as_ref() {
                    Identifier::Simple { symbol } => ctx
                        .const_sort(symbol)
                        .cloned()
                        .ok_or_else(|| UnknownSort(Term::Variable(self.into()))),
                    Identifier::Indexed { symbol, indices } => {
                        // Check for (_ bvX n) literals
                        match indices.as_slice() {
                            [Index::Numeral(n)] if symbol.0.starts_with("bv") => {
                                Ok(ISort::bitvec(n.clone()))
                            }
                            _ => Err(UnknownSort(Term::Variable(self.into()))),
                        }
                    }
                }
            }
            Self::Sorted { sort, .. } => Ok(sort.clone()),
        }
    }
}

impl<L: Logic> Sorted<L> for CoreOp<Term<L>> {
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        if let Self::Ite(_, t, e) = self {
            let sort = t.sort(ctx)?;
            debug_assert_eq!(e.sort(ctx)?, sort, "ite branches must be of the same sort");
            Ok(sort)
        } else {
            Ok(ISort::bool())
        }
    }
}

impl<L: Logic> Sorted<L> for IQuantifier<L> {
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        self.as_ref().sort(ctx)
    }
}

impl<L: Logic> Sorted<L> for ICoreOp<L> {
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        self.as_ref().sort(ctx)
    }
}

impl<L: Logic> Sorted<L> for IOp<L> {
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        self.as_ref().sort(ctx)
    }
}

impl<L: Logic> Sorted<L> for Void {
    fn sort(&self, _: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        match *self {}
    }
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
#[error("unknown sort for: {0}")]
pub struct UnknownSort<T: Debug + Display>(pub T);

impl<L: Logic> Folder<L> for SortChecker<'_> {
    type Output = ISort;
    type Error = UnknownSort<Term<L>>;

    fn fold_const(&mut self, constant: crate::IConst) -> Result<Self::Output, Self::Error> {
        match constant.as_ref() {
            Constant::Numeral(_) => Ok(ISort::int()),
            Constant::String(_) => Ok(ISort::string()),
            Constant::Binary(bits) => Ok(ISort::bitvec(bits.len().into())),
            Constant::Hexadecimal(digits) => Ok(ISort::bitvec((digits.len() * 4).into())),
            Constant::Decimal(_) => Ok(ISort::real()),
        }
    }

    fn fold_var(&mut self, var: crate::IVar<L::Var>) -> Result<Self::Output, Self::Error> {
        var.sort(&mut self.0)
    }

    fn fold_core_op(&mut self, op: ICoreOp<L>) -> Result<Self::Output, Self::Error> {
        op.sort(&mut self.0)
    }

    fn fold_theory_op(&mut self, op: crate::IOp<L>) -> Result<Self::Output, Self::Error> {
        op.sort(&mut self.0)
    }

    fn fold_uninterpreted_func(&mut self, uf: crate::IUF<L>) -> Result<Self::Output, Self::Error> {
        uf.sort(&mut self.0)
    }

    fn fold_let(&mut self, l: crate::ILet<L>) -> Result<Self::Output, Self::Error> {
        l.term.sort(&mut self.0)
    }

    fn fold_match(&mut self, m: crate::IMatch<L>) -> Result<Self::Output, Self::Error> {
        Err(UnknownSort(m.into()))
    }

    fn fold_quantifier(&mut self, quantifier: IQuantifier<L>) -> Result<Self::Output, Self::Error> {
        quantifier.sort(&mut self.0)
    }
}
