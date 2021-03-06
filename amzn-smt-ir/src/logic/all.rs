// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::{ArithOp, ArrayOp, BvOp, StringOp};
use crate::{Logic, QualIdentifier, Quantifier, Term, UF};

combine_ops! {
    pub enum Op<Term> {
        Arith(ArithOp<Term>),
        Array(ArrayOp<Term>),
        BitVec(BvOp<Term>),
        String(StringOp<Term>),
    }
}

#[cfg(test)]
mod size_assertions {
    use super::*;
    static_assertions::assert_eq_size!(Op<Term>, [*const (); 8]);
    static_assertions::assert_eq_size!(ArithOp<Term>, [*const (); 6]);
    static_assertions::assert_eq_size!(ArrayOp<Term>, [*const (); 7]);
    static_assertions::assert_eq_size!(BvOp<Term>, [*const (); 6]);
    static_assertions::assert_eq_size!(StringOp<Term>, [*const (); 7]);
}

#[derive(Clone, Default, Debug, Hash, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub struct ALL;

impl Logic for ALL {
    type Var = QualIdentifier;
    type Op = Op<Term<Self>>;
    type UninterpretedFunc = UF<Term<Self>>;
    type Quantifier = Quantifier<Term<Self>>;
}
