// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    fold::Fold, visit::Visit, Ctx, IOp, ISort, Logic, Operation, QualIdentifier, Sorted, Term,
    UnknownSort, Void,
};

#[derive(Operation, Visit, Fold, Clone, PartialEq, Eq, Hash)]
pub enum ArrayOp<Term> {
    Select(Term, Term),
    Store(Term, Term, Term),
}

impl<L: Logic> Sorted<L> for ArrayOp<Term<L>>
where
    Self: Into<L::Op>,
{
    fn sort(&self, _: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        Err(UnknownSort(IOp::<L>::new(self.clone().into()).into()))
    }
}

#[derive(Clone, Default, Debug, Hash, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub struct QF_AX;

impl Logic for QF_AX {
    type Var = QualIdentifier;
    type Op = ArrayOp<Term<Self>>;
    type Quantifier = Void;
    type UninterpretedFunc = Void;
}
