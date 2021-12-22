// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::int_term;
use amzn_smt_ir::{
    chained,
    fold::{Fold, IntraLogicFolder, SuperFold},
    logic::{
        all::{Op, ALL},
        ArithOp,
    },
    pairwise, Constant, CoreOp, Ctx, HashOrdered, ICoreOp, ILet, IOp, ISort, Sorted, Term,
    UnknownSort,
};
use either::Either;
use num_traits::{One, Zero};
use smallvec::{smallvec, SmallVec};
use smt2parser::Numeral;
use std::{collections::BTreeMap, iter};

pub struct Canonicalizer<'a> {
    context: &'a mut Ctx,
    pub(super) new_asserts: Vec<Term>,
}

impl<'a> Canonicalizer<'a> {
    pub fn new(ctx: &'a mut Ctx) -> Self {
        Self {
            context: ctx,
            new_asserts: Default::default(),
        }
    }

    fn negate(t: Term) -> Term {
        use ArithOp::*;
        use Op::*;

        match &t {
            Term::OtherOp(op) => match op.as_ref() {
                Arith(Plus(args)) => Plus(args.iter().cloned().map(Self::negate).collect()).into(),
                Arith(Neg(arg)) => arg.clone(),
                Arith(Mul(args)) => match args.as_slice() {
                    [c @ Term::Constant(..), v @ Term::Variable(..)] => {
                        Mul([Neg(c.clone()).into(), v.clone()].into()).into()
                    }
                    [Term::OtherOp(c), v @ Term::Variable(..)] => match c.as_ref() {
                        Arith(Neg(c @ Term::Constant(..))) => {
                            Mul([c.clone(), v.clone()].into()).into()
                        }
                        _ => Neg(t).into(),
                    },
                    _ => Neg(t).into(),
                },
                _ => Neg(t).into(),
            },
            _ => Neg(t).into(),
        }
    }

    fn canonicalize_plus_inner(
        args: impl IntoIterator<Item = Term>,
    ) -> (SmallVec<[Term; 2]>, Numeral, Numeral) {
        use ArithOp::*;
        use Op::*;

        fn group_same_vars(terms: impl IntoIterator<Item = Term>) -> SmallVec<[Term; 2]> {
            let mut map: BTreeMap<HashOrdered<_>, (Numeral, Numeral)> = BTreeMap::new();
            let mut res = smallvec![];

            for t in terms {
                match t {
                    Term::Variable(v) => {
                        let (pos, _) = map.entry(HashOrdered(v)).or_default();
                        *pos += Numeral::from(1u8);
                    }
                    Term::OtherOp(op) => match op.as_ref() {
                        Arith(Neg(t)) => {
                            if let Term::Variable(v) = t {
                                let (_, neg) = map.entry(HashOrdered(v.clone())).or_default();
                                *neg += Numeral::from(1u8);
                            } else {
                                res.push(Neg(t.clone()).into());
                            }
                        }
                        Arith(Mul(args)) => match args.as_slice() {
                            [Term::Constant(c), Term::Variable(v)] => match c.as_ref() {
                                Constant::Numeral(a) => {
                                    let (pos, _) = map.entry(HashOrdered(v.clone())).or_default();
                                    *pos += a;
                                }
                                _ => res.push(op.into()),
                            },
                            [Term::OtherOp(c), Term::Variable(v)] => match c.as_ref() {
                                Arith(Neg(Term::Constant(c))) => match c.as_ref() {
                                    Constant::Numeral(a) => {
                                        let (_, neg) =
                                            map.entry(HashOrdered(v.clone())).or_default();
                                        *neg += a;
                                    }
                                    _ => res.push(op.into()),
                                },
                                _ => res.push(op.into()),
                            },
                            _ => res.push(op.into()),
                        },
                        _ => res.push(op.into()),
                    },
                    _ => res.push(t),
                }
            }

            use std::cmp::Ordering::*;
            res.extend(
                map.into_iter()
                    .map(|(HashOrdered(v), (pos, neg))| match pos.cmp(&neg) {
                        Less => {
                            let x = neg - pos;
                            if x.is_one() {
                                Canonicalizer::negate(v.into())
                            } else {
                                let neg_coeff = Canonicalizer::negate(Constant::Numeral(x).into());
                                Mul([neg_coeff, v.into()].into()).into()
                            }
                        }
                        Greater => {
                            let x = pos - neg;
                            if x.is_one() {
                                v.into()
                            } else {
                                Mul([Constant::Numeral(x).into(), v.into()].into()).into()
                            }
                        }
                        Equal => v.into(),
                    }),
            );
            res
        }

        let mut c_pos = Numeral::zero();
        let mut c_neg = Numeral::zero();
        let args = args
            .into_iter()
            // flatten nested plus operators
            .flat_map(|arg| {
                if let Term::OtherOp(op) = &arg {
                    if let Arith(Plus(args)) = op.as_ref() {
                        return Either::Left(args.clone().into_iter());
                    }
                }
                Either::Right(iter::once(arg))
            })
            // pull out constants
            .filter(|arg| {
                if let Some((x, pos)) = int_term(arg) {
                    if pos {
                        c_pos += x;
                    } else {
                        c_neg += x;
                    }
                    false
                } else {
                    true
                }
            });
        (group_same_vars(args), c_pos, c_neg)
    }

    fn canonicalize_plus(args: impl IntoIterator<Item = Term>) -> Term {
        use ArithOp::*;

        let (mut args, c_pos, c_neg) = Self::canonicalize_plus_inner(args);
        use std::cmp::Ordering::*;
        match c_pos.cmp(&c_neg) {
            Less => args.push(Self::negate(Constant::Numeral(c_neg - c_pos).into())),
            Greater => args.push(Constant::Numeral(c_pos - c_neg).into()),
            Equal => (),
        }
        Plus(args).into()
    }

    fn normalize_constraint(l: Term, r: Term) -> (Term, Term) {
        use ArithOp::*;
        use Op::*;

        let (mut args, pos, neg) =
            Self::canonicalize_plus_inner(iter::once(l).chain(iter::once(Self::negate(r))));
        use std::cmp::Ordering::*;
        let rhs = match pos.cmp(&neg) {
            Less => Constant::Numeral(neg - pos).into(),
            Greater => Self::negate(Constant::Numeral(pos - neg).into()),
            Equal => {
                if args.len() > 1 {
                    let mut to_move = 0;
                    for (i, t) in args.iter().enumerate() {
                        if let Term::OtherOp(op) = t {
                            if let Arith(Neg(..)) = op.as_ref() {
                                to_move = i;
                                break;
                            }
                        }
                    }
                    Self::negate(args.swap_remove(to_move))
                } else {
                    Constant::Numeral(Numeral::zero()).into()
                }
            }
        };
        (Plus(args).into(), rhs)
    }
}

impl IntraLogicFolder<ALL> for Canonicalizer<'_> {
    type Error = anyhow::Error;

    fn context(&self) -> Option<&Ctx> {
        Some(self.context)
    }
    fn context_mut(&mut self) -> Option<&mut Ctx> {
        Some(self.context)
    }

    fn fold_core_op(&mut self, op: ICoreOp<ALL>) -> Result<Term, Self::Error> {
        let implies = |a: Term, b: Term| CoreOp::Imp([a, b].into()).into();
        Ok(match op.super_fold_with(self)? {
            CoreOp::Eq(args) => {
                let sort = (args.first())
                    .ok_or_else(|| UnknownSort(CoreOp::Eq(args.clone()).into()))
                    .and_then(|arg| arg.sort(self.context));
                if sort == Ok(ISort::int()) {
                    chained(args, |l, r| {
                        let (l, r) = Self::normalize_constraint(l, r);
                        CoreOp::Eq([l, r].into()).into()
                    })
                } else {
                    CoreOp::Eq(args).into()
                }
            }
            // TODO: can the bound be computed with `ite` and `distinct` applications left as-is?
            CoreOp::Ite(cond, consq, alt) => {
                let sort = consq.sort(self.context)?;
                debug_assert_eq!(
                    alt.sort(self.context)?,
                    sort,
                    "ite branches are of different sorts"
                );
                if sort == ISort::int() {
                    let res = Term::from(self.context.fresh_var(sort)?);
                    let if_true = {
                        let (l, r) = Self::normalize_constraint(res.clone(), consq);
                        CoreOp::Eq([l, r].into()).into()
                    };
                    self.new_asserts.push(implies(cond.clone(), if_true));
                    let if_false = {
                        let (l, r) = Self::normalize_constraint(res.clone(), alt);
                        CoreOp::Eq([l, r].into()).into()
                    };
                    self.new_asserts.push(implies(!cond, if_false));
                    res
                } else {
                    implies(cond.clone(), consq) & implies(!cond, alt)
                }
            }
            CoreOp::Distinct(args) => {
                let sort = (args.first())
                    .ok_or_else(|| UnknownSort(CoreOp::Distinct(args.clone()).into()))
                    .and_then(|arg| arg.sort(self.context));
                if sort == Ok(ISort::int()) {
                    pairwise(&args, |x, y| {
                        let (l, r) = Self::normalize_constraint(x, y);
                        !Term::from(CoreOp::Eq([l, r].into()))
                    })
                } else {
                    CoreOp::Distinct(args).into()
                }
            }
            op => op.into(),
        })
    }

    fn fold_theory_op(&mut self, op: IOp<ALL>) -> Result<Term, Self::Error> {
        use ArithOp::*;
        use Op::*;

        let normalize_gte = |l, r| {
            let (l, r) = Self::normalize_constraint(l, r);
            Gte([l, r].into()).into()
        };
        let op = match op.super_fold_with(self)? {
            Arith(Plus(args)) => Self::canonicalize_plus(args),
            Arith(Neg(arg)) => Self::negate(arg),
            Arith(Minus(args)) => {
                // x - y - z = x + (-y) + (-z)
                let mut args = args.into_iter();
                Self::canonicalize_plus(args.next().into_iter().chain(args.map(Self::negate)))
            }
            // Only (* x c) or (* c x) are allowed, we expect (* c x)
            Arith(Mul(mut args)) => match args.as_slice() {
                [_, b] => {
                    if int_term(b).is_some() {
                        args.swap(0, 1);
                    }
                    Mul(args).into()
                }
                _ => anyhow::bail!("term invalid in LIA: {}", Mul(args)),
            },
            Arith(Gte(args)) => chained(args, |l, r| normalize_gte(l, r)),
            Arith(Gt(args)) => chained(args, |l, r| !normalize_gte(r, l)),
            Arith(Lte(args)) => chained(args, |l, r| normalize_gte(r, l)),
            Arith(Lt(args)) => chained(args, |l, r| !normalize_gte(l, r)),
            op => op.into(),
        };
        Ok(op)
    }

    fn fold_let(&mut self, l: ILet<ALL>) -> Result<Term, Self::Error> {
        l.term.clone().substitute(&l.bindings).fold_with(self)
    }
}

#[test]
fn canonicalization() {
    use amzn_smt_ir::Script;
    let assert_canonical = |orig: &str, canon: &str| {
        assert_eq!(
            Script::<Term>::parse(orig.as_bytes())
                .unwrap()
                .try_fold(&mut Canonicalizer::new(&mut Ctx::default()))
                .unwrap(),
            Script::parse(canon.as_bytes()).unwrap(),
        )
    };
    assert_canonical("(assert (>= x 5))", "(assert (>= (+ x) 5))");
    assert_canonical("(assert (>= (+ x x) 5))", "(assert (>= (+ (* 2 x)) 5))");
    assert_canonical("(assert (>= (+ x (+ x)) 5))", "(assert (>= (+ (* 2 x)) 5))");
    assert_canonical("(assert (>= 5 x))", "(assert (>= (+ (- x)) (- 5)))");
    assert_canonical(
        "(assert (>= (+ x (+ x 2 x) 2 (+ x)) 5))",
        "(assert (>= (+ (* 4 x)) 1))",
    );
}
