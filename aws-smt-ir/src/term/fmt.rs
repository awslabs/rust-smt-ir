use super::{IVar, Logic, Term};
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::Internable;
use std::fmt;

impl<T: Internable + fmt::Debug> fmt::Debug for IVar<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Internable + fmt::Display> fmt::Display for IVar<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Logic> fmt::Debug for Term<T>
where
    T::Var: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(c) => write!(f, "{}", c),
            Self::Variable(v) => write!(f, "{}", v),
            Self::CoreOp(op) => op.fmt(f),
            Self::OtherOp(op) => op.fmt(f),
            Self::UF(uf) => uf.fmt(f),
            Self::Let(l) => l.fmt(f),
            Self::Match(m) => m.fmt(f),
            Self::Quantifier(q) => q.fmt(f),
        }
    }
}

impl<T: Logic> fmt::Display for Term<T>
where
    T::Var: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(c) => c.fmt(f),
            Self::Variable(v) => v.fmt(f),
            Self::CoreOp(op) => op.fmt(f),
            Self::OtherOp(op) => op.fmt(f),
            Self::UF(uf) => uf.fmt(f),
            Self::Let(l) => l.fmt(f),
            Self::Match(m) => m.fmt(f),
            Self::Quantifier(q) => q.fmt(f),
        }
    }
}
