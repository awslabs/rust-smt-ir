// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    fold::Fold, visit::Visit, Ctx, IOp, ISort, Logic, Operation, QualIdentifier, SmallVec, Sorted,
    Term, UnknownSort, Void,
};

type Args<T> = SmallVec<[T; 2]>;

#[derive(Operation, Visit, Fold, Clone, PartialEq, Eq, Hash)]
pub enum SetOp<Term> {
    // Empty(Term, Term),
    #[symbol("set.insert")]
    Insert(Args<Term>),
    #[symbol("set.union")]
    Union(Term, Term),
    #[symbol("set.inter")]
    Inter(Term, Term),
    #[symbol("set.minus")]
    Minus(Term, Term),
    #[symbol("set.member")]
    Member(Term, Term),
    #[symbol("set.subset")]
    Subset(Term, Term),
    #[symbol("set.singleton")]
    Singleton(Term),
    #[symbol("set.card")]
    Card(Term),
    #[symbol("set.complement")]
    Complement(Term),
}

impl<L: Logic> Sorted<L> for SetOp<Term<L>>
where
    Self: Into<L::Op>,
{
    fn sort(&self, _: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        Err(UnknownSort(IOp::<L>::new(self.clone().into()).into()))
    }
}

#[derive(Clone, Default, Debug, Hash, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub struct QF_F;

impl Logic for QF_F {
    type Var = QualIdentifier;
    type Op = SetOp<Term<Self>>;
    type Quantifier = Void;
    type UninterpretedFunc = Void;
}
