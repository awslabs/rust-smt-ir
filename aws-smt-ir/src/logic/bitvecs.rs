// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::smt2parser::Numeral;
use crate::{
    fold::Fold, visit::Visit, Ctx, IIndex, ISort, Index, Logic, Operation, QualIdentifier, Sorted,
    Term, UnknownSort, Void, UF,
};
use num_traits::One;
use smallvec::SmallVec;

type Args<T> = SmallVec<[T; 2]>;

#[derive(Operation, Visit, Fold, Clone, PartialEq, Eq, Hash)]
pub enum BvOp<Term> {
    Concat(Term, Term),
    Extract([IIndex; 2], Term),
    BvNot(Term),
    BvNeg(Term),
    BvAnd(Args<Term>),
    BvOr(Args<Term>),
    BvAdd(Args<Term>),
    BvMul(Args<Term>),
    BvUdiv(Term, Term),
    BvUrem(Term, Term),
    BvShl(Term, Term),
    BvLshr(Term, Term),
    BvUlt(Term, Term),
    /// (bvnand (_ BitVec m) (_ BitVec m) (_ BitVec m))
    ///  - bitwise nand (negation of and)
    BvNand(Term, Term),
    /// (bvnor (_ BitVec m) (_ BitVec m) (_ BitVec m))
    ///  - bitwise nor (negation of or)
    BvNor(Term, Term),
    /// (bvxor (_ BitVec m) (_ BitVec m) (_ BitVec m))
    ///  - bitwise exclusive or
    BvXor(Args<Term>),
    /// (bvxnor (_ BitVec m) (_ BitVec m) (_ BitVec m))
    ///  - bitwise equivalence (equivalently, negation of bitwise exclusive or)
    BvXnor(Term, Term),
    /// (bvcomp (_ BitVec m) (_ BitVec m) (_ BitVec 1))
    ///  - bit comparator: equals #b1 iff all bits are equal
    BvComp(Term, Term),
    /// (bvsub (_ BitVec m) (_ BitVec m) (_ BitVec m))
    ///  - 2's complement subtraction modulo 2^m
    BvSub(Term, Term),
    /// (bvsdiv (_ BitVec m) (_ BitVec m) (_ BitVec m))
    ///  - 2's complement signed division
    BvSdiv(Term, Term),
    /// (bvsrem (_ BitVec m) (_ BitVec m) (_ BitVec m))
    ///  - 2's complement signed remainder (sign follows dividend)
    BvSrem(Term, Term),
    /// (bvsmod (_ BitVec m) (_ BitVec m) (_ BitVec m))
    ///  - 2's complement signed remainder (sign follows divisor)
    BvSmod(Term, Term),
    /// (bvashr (_ BitVec m) (_ BitVec m) (_ BitVec m))
    ///  - Arithmetic shift right, like logical shift right except that the most
    ///    significant bits of the result always copy the most significant
    ///    bit of the first argument.
    BvAshr(Term, Term),
    /// ((_ repeat i) (_ BitVec m) (_ BitVec i*m))
    ///  - ((_ repeat i) x) means concatenate i copies of x
    Repeat([IIndex; 1], Term),
    /// ((_ zero_extend i) (_ BitVec m) (_ BitVec m+i))
    ///  - ((_ zero_extend i) x) means extend x with zeroes to the (unsigned)
    ///    equivalent bitvector of size m+i
    #[symbol("zero_extend")]
    ZeroExtend([IIndex; 1], Term),
    /// ((_ sign_extend i) (_ BitVec m) (_ BitVec m+i))
    ///  - ((_ sign_extend i) x) means extend x to the (signed) equivalent bitvector
    ///    of size m+i
    #[symbol("sign_extend")]
    SignExtend([IIndex; 1], Term),
    /// ((_ rotate_left i) (_ BitVec m) (_ BitVec m))
    ///  - ((_ rotate_left i) x) means rotate bits of x to the left i times
    #[symbol("rotate_left")]
    RotateLeft([IIndex; 1], Term),
    /// ((_ rotate_right i) (_ BitVec m) (_ BitVec m))
    ///  - ((_ rotate_right i) x) means rotate bits of x to the right i times
    #[symbol("rotate_right")]
    RotateRight([IIndex; 1], Term),
    /// (bvule (_ BitVec m) (_ BitVec m) Bool)
    ///  - binary predicate for unsigned less than or equal
    BvUle(Term, Term),
    /// (bvugt (_ BitVec m) (_ BitVec m) Bool)
    ///  - binary predicate for unsigned greater than
    BvUgt(Term, Term),
    /// (bvuge (_ BitVec m) (_ BitVec m) Bool)
    ///  - binary predicate for unsigned greater than or equal
    BvUge(Term, Term),
    /// (bvslt (_ BitVec m) (_ BitVec m) Bool)
    ///  - binary predicate for signed less than
    BvSlt(Term, Term),
    /// (bvsle (_ BitVec m) (_ BitVec m) Bool)
    ///  - binary predicate for signed less than or equal
    BvSle(Term, Term),
    /// (bvsgt (_ BitVec m) (_ BitVec m) Bool)
    ///  - binary predicate for signed greater than
    BvSgt(Term, Term),
    /// (bvsge (_ BitVec m) (_ BitVec m) Bool)
    ///  - binary predicate for signed greater than or equal
    BvSge(Term, Term),
}

impl<L: Logic> Sorted<L> for BvOp<Term<L>>
where
    Self: Into<L::Op>,
{
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        use BvOp::*;

        let unknown = || UnknownSort(Term::from(self.clone()));
        macro_rules! bvwidth {
            ($sort:expr) => {
                $sort.bv_width().ok_or_else(unknown)
            };
        }

        Ok(match self {
            Concat(l, r) => {
                let (l, r) = (l.sort(ctx)?, r.sort(ctx)?);
                let (i, j) = (bvwidth!(&l)?, bvwidth!(&r)?);
                ISort::bitvec(i + j)
            }
            Extract([i, j], _) => match (i.as_ref(), j.as_ref()) {
                (Index::Numeral(i), Index::Numeral(j)) => ISort::bitvec(Numeral::one() + i - j),
                _ => return Err(unknown()),
            },
            BvNot(arg) | BvNeg(arg) => arg.sort(ctx)?,
            BvAnd(args) | BvOr(args) | BvAdd(args) | BvMul(args) | BvXor(args) => {
                let sort = args.first().ok_or_else(unknown)?.sort(ctx)?;
                #[cfg(debug_assertions)]
                for arg in args.iter().skip(1) {
                    assert_eq!(arg.sort(ctx)?, sort);
                }
                sort
            }
            BvUdiv(l, r)
            | BvUrem(l, r)
            | BvShl(l, r)
            | BvLshr(l, r)
            | BvNand(l, r)
            | BvNor(l, r)
            | BvXnor(l, r)
            | BvSub(l, r)
            | BvSdiv(l, r)
            | BvSrem(l, r)
            | BvSmod(l, r)
            | BvAshr(l, r) => {
                let sort = l.sort(ctx)?;
                debug_assert_eq!(r.sort(ctx)?, sort);
                sort
            }
            BvUlt(..) | BvUle(..) | BvUgt(..) | BvUge(..) | BvSlt(..) | BvSle(..) | BvSgt(..)
            | BvSge(..) => ISort::bool(),
            BvComp(..) => ISort::bitvec(Numeral::one()),
            Repeat([i], arg) => match i.as_ref() {
                Index::Numeral(i) => {
                    let sort = arg.sort(ctx)?;
                    ISort::bitvec(i * bvwidth!(&sort)?)
                }
                _ => return Err(unknown()),
            },
            ZeroExtend([i], arg) | SignExtend([i], arg) => match i.as_ref() {
                Index::Numeral(i) => {
                    let sort = arg.sort(ctx)?;
                    ISort::bitvec(i + bvwidth!(&sort)?)
                }
                _ => return Err(unknown()),
            },
            RotateLeft(_, arg) | RotateRight(_, arg) => arg.sort(ctx)?,
        })
    }
}

#[derive(Clone, Default, Debug, Hash, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub struct QF_BV;

impl Logic for QF_BV {
    type Var = QualIdentifier;
    type Op = BvOp<Term<Self>>;
    type Quantifier = Void;
    type UninterpretedFunc = Void;
}

#[derive(Clone, Default, Debug, Hash, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub struct QF_UFBV;

impl Logic for QF_UFBV {
    type Var = QualIdentifier;
    type Op = BvOp<Term<Self>>;
    type Quantifier = Void;
    type UninterpretedFunc = UF<Term<Self>>;
}
