// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::{Fold, Folder};
use crate::{IConst, ICoreOp, ILet, IMatch, IOp, IQuantifier, IVar, Logic, IUF};
use std::{
    convert::{identity, Infallible},
    marker::PhantomData,
};

pub trait Compose: Sized {
    fn compose<After, M1, M2>(self, after: After) -> Composed<Self, After, M1, M2> {
        TryComposed::new(self, after, identity, identity)
    }

    fn try_compose<After, MapErr1, MapErr2, Err, M1, M2>(
        self,
        after: After,
        f: MapErr1,
        g: MapErr2,
    ) -> TryComposed<Self, After, MapErr1, MapErr2, Err, M1, M2> {
        TryComposed::new(self, after, f, g)
    }
}

impl<T> Compose for T {}

type Composed<Before, After, M1, M2> = TryComposed<
    Before,
    After,
    fn(Infallible) -> Infallible,
    fn(Infallible) -> Infallible,
    Infallible,
    M1,
    M2,
>;

pub struct TryComposed<Before, After, MapErr1, MapErr2, Err, M1, M2> {
    before: Before,
    after: After,
    map_err1: MapErr1,
    map_err2: MapErr2,
    err: PhantomData<Err>,
    m1: PhantomData<M1>,
    m2: PhantomData<M2>,
}

impl<Before, After, MapErr1, MapErr2, Err, M1, M2>
    TryComposed<Before, After, MapErr1, MapErr2, Err, M1, M2>
{
    const fn new(before: Before, after: After, map_err1: MapErr1, map_err2: MapErr2) -> Self {
        Self {
            before,
            after,
            map_err1,
            map_err2,
            err: PhantomData,
            m1: PhantomData,
            m2: PhantomData,
        }
    }
}

impl<L: Logic, Before, After, MapErr1, MapErr2, Err, M1, M2> Folder<L>
    for TryComposed<Before, After, MapErr1, MapErr2, Err, M1, M2>
where
    Before: Folder<L, M1>,
    Before::Output: Fold<L, After::Output, Output = After::Output>,
    After: Folder<L, M2>,
    MapErr1: FnMut(Before::Error) -> Err,
    MapErr2: FnMut(After::Error) -> Err,
{
    type Output = After::Output;
    type Error = Err;

    fn fold_const(&mut self, constant: IConst) -> Result<Self::Output, Self::Error> {
        let t = constant
            .fold_with(&mut self.before)
            .map_err(&mut self.map_err1)?;
        t.fold_with(&mut self.after).map_err(&mut self.map_err2)
    }

    fn fold_var(&mut self, var: IVar<L::Var>) -> Result<Self::Output, Self::Error> {
        let t = var
            .fold_with(&mut self.before)
            .map_err(&mut self.map_err1)?;
        t.fold_with(&mut self.after).map_err(&mut self.map_err2)
    }

    fn fold_core_op(&mut self, op: ICoreOp<L>) -> Result<Self::Output, Self::Error> {
        let t = op.fold_with(&mut self.before).map_err(&mut self.map_err1)?;
        t.fold_with(&mut self.after).map_err(&mut self.map_err2)
    }

    fn fold_theory_op(&mut self, op: IOp<L>) -> Result<Self::Output, Self::Error> {
        let t = op.fold_with(&mut self.before).map_err(&mut self.map_err1)?;
        t.fold_with(&mut self.after).map_err(&mut self.map_err2)
    }

    fn fold_uninterpreted_func(&mut self, func: IUF<L>) -> Result<Self::Output, Self::Error> {
        let t = func
            .fold_with(&mut self.before)
            .map_err(&mut self.map_err1)?;
        t.fold_with(&mut self.after).map_err(&mut self.map_err2)
    }

    fn fold_let(&mut self, l: ILet<L>) -> Result<Self::Output, Self::Error> {
        let t = l.fold_with(&mut self.before).map_err(&mut self.map_err1)?;
        t.fold_with(&mut self.after).map_err(&mut self.map_err2)
    }

    fn fold_match(&mut self, m: IMatch<L>) -> Result<Self::Output, Self::Error> {
        let t = m.fold_with(&mut self.before).map_err(&mut self.map_err1)?;
        t.fold_with(&mut self.after).map_err(&mut self.map_err2)
    }

    fn fold_quantifier(&mut self, q: IQuantifier<L>) -> Result<Self::Output, Self::Error> {
        let t = q.fold_with(&mut self.before).map_err(&mut self.map_err1)?;
        t.fold_with(&mut self.after).map_err(&mut self.map_err2)
    }
}
