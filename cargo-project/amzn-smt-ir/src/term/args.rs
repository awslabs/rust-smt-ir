//! Traits representing the required behavior for types to be used as operator arguments.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::{IConst, IVar, Logic, Term};
use crate::{Internable, Void, UF};
use smallvec::SmallVec;
use std::{convert::TryInto, fmt, iter, slice, vec};

/// `Parse` represents the ability of a type to be parsed from an iterator of SMT-LIB terms.
/// If `Self` contains a single argument, this likely just consists of consuming the next element
/// from the iterator and converting it; if `Self` contains multiple, then the implementation may
/// consume multiple iterator elements.
pub trait Parse<L: Logic>: Sized + NumArgs {
    /// Parses `Self` from an iterator of SMT-LIB [`Term`]s.
    fn from_iter<I: IntoIterator<Item = Term<L>>>(iter: I) -> Option<Self>;
}

pub trait NumArgs {
    /// Minimum number of arguments `Self` can contain.
    const MIN_ARGS: usize;
    /// Maximum number of arguments `Self` can contain.
    const MAX_ARGS: usize;
}

pub trait Iterate<'a, L: Logic> {
    type Terms: Iterator<Item = &'a Term<L>> + 'a;
    type IntoTerms: Iterator<Item = Term<L>> + 'a;

    fn terms(&'a self) -> Self::Terms;
    fn into_terms(self) -> Self::IntoTerms;
}

pub trait Arguments<'a, L: Logic>: Iterate<'a, L> + Sized {
    fn args(&'a self) -> Self::Terms {
        <Self as Iterate<'a, L>>::terms(self)
    }
    fn into_args(self) -> Self::IntoTerms {
        <Self as Iterate<'a, L>>::into_terms(self)
    }
}

/// `Format` represents the ability of a type to be formatted as an s-expression.
pub trait Format {
    /// Type of the argument(s) contained within `Self`. If `Self` contains a single argument, e.g.
    /// `Box<T>`, then `Inner` can be `Self`; if `Self` contains multiple arguments, e.g. `Vec<T>`,
    /// then `Inner` is the type of an individual argument (i.e. `T`).
    type Inner: fmt::Debug + fmt::Display;

    /// Writes an s-expression representation of `self` to the formatter `f` using `fmt_inner` to
    /// format individual arguments.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        fmt_inner: impl FnMut(&Self::Inner, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result;
}

impl<L: Logic> Parse<L> for IConst {
    fn from_iter<I: IntoIterator<Item = Term<L>>>(iter: I) -> Option<Self> {
        let item = iter.into_iter().next()?;
        match item {
            Term::Constant(c) => Some(c),
            _ => None,
        }
    }
}

impl NumArgs for IConst {
    const MIN_ARGS: usize = 1;
    const MAX_ARGS: usize = 1;
}

impl Format for IConst {
    type Inner = Self;

    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        mut fmt_inner: impl FnMut(&Self::Inner, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        fmt_inner(self, f)
    }
}

impl<L: Logic> Parse<L> for IVar<L::Var> {
    fn from_iter<I: IntoIterator<Item = Term<L>>>(iter: I) -> Option<Self> {
        let item = iter.into_iter().next()?;
        match item {
            Term::Variable(v) => Some(v),
            _ => None,
        }
    }
}

impl<T: Internable> NumArgs for IVar<T> {
    const MIN_ARGS: usize = 1;
    const MAX_ARGS: usize = 1;
}

impl<T: Internable + fmt::Debug + fmt::Display> Format for IVar<T> {
    type Inner = Self;

    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        mut fmt_inner: impl FnMut(&Self::Inner, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        fmt_inner(self, f)
    }
}

impl<L: Logic> Parse<L> for Term<L> {
    fn from_iter<I: IntoIterator<Item = Term<L>>>(iter: I) -> Option<Self> {
        iter.into_iter().next()
    }
}

impl<'a, L: Logic> Iterate<'a, L> for Term<L> {
    type Terms = iter::Once<&'a Self>;
    type IntoTerms = iter::Once<Self>;

    fn terms(&'a self) -> Self::Terms {
        iter::once(self)
    }
    fn into_terms(self) -> Self::IntoTerms {
        iter::once(self)
    }
}

impl<L: Logic> NumArgs for Term<L> {
    const MIN_ARGS: usize = 1;
    const MAX_ARGS: usize = 1;
}

impl<T: Logic> Format for Term<T> {
    type Inner = Self;

    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        mut fmt_inner: impl FnMut(&Self::Inner, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        fmt_inner(self, f)
    }
}

impl<L: Logic, T: Parse<L>> Parse<L> for Box<[T]>
where
    Term<L>: TryInto<T>,
{
    fn from_iter<I: IntoIterator<Item = Term<L>>>(iter: I) -> Option<Self> {
        iter.into_iter().map(|t| t.try_into().ok()).collect()
    }
}

impl<T: NumArgs> NumArgs for Box<[T]> {
    const MIN_ARGS: usize = 0;
    const MAX_ARGS: usize = usize::MAX;
}

impl<T: fmt::Debug + fmt::Display> Format for Box<[T]> {
    type Inner = T;

    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        mut fmt_inner: impl FnMut(&Self::Inner, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        let mut args = self.iter();
        if let Some(arg) = args.next() {
            fmt_inner(arg, f)?;
        }
        for arg in args {
            write!(f, " ")?;
            fmt_inner(arg, f)?;
        }
        Ok(())
    }
}

impl<L: Logic, T> Parse<L> for Vec<T>
where
    Term<L>: TryInto<T>,
{
    fn from_iter<I: IntoIterator<Item = Term<L>>>(iter: I) -> Option<Self> {
        iter.into_iter().map(|t| t.try_into().ok()).collect()
    }
}

impl<'a, L: Logic> Iterate<'a, L> for Vec<Term<L>> {
    type Terms = slice::Iter<'a, Term<L>>;
    type IntoTerms = std::vec::IntoIter<Term<L>>;

    fn terms(&'a self) -> Self::Terms {
        self.iter()
    }
    fn into_terms(self) -> Self::IntoTerms {
        self.into_iter()
    }
}

impl<T> NumArgs for Vec<T> {
    const MIN_ARGS: usize = 0;
    const MAX_ARGS: usize = usize::MAX;
}

impl<T: fmt::Debug + fmt::Display> Format for Vec<T> {
    type Inner = T;

    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        mut fmt_inner: impl FnMut(&Self::Inner, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        let mut args = self.iter();
        if let Some(arg) = args.next() {
            fmt_inner(arg, f)?;
        }
        for arg in args {
            write!(f, " ")?;
            fmt_inner(arg, f)?;
        }
        Ok(())
    }
}

impl<L: Logic, A: smallvec::Array> Parse<L> for SmallVec<A>
where
    Term<L>: TryInto<A::Item>,
{
    fn from_iter<I: IntoIterator<Item = Term<L>>>(iter: I) -> Option<Self> {
        iter.into_iter().map(|t| t.try_into().ok()).collect()
    }
}

impl<'a, L: Logic, A> Iterate<'a, L> for SmallVec<A>
where
    A: smallvec::Array<Item = Term<L>> + 'a,
{
    type Terms = slice::Iter<'a, Term<L>>;
    type IntoTerms = smallvec::IntoIter<A>;

    fn terms(&'a self) -> Self::Terms {
        self.iter()
    }
    fn into_terms(self) -> Self::IntoTerms {
        self.into_iter()
    }
}

impl<A: smallvec::Array> NumArgs for SmallVec<A> {
    const MIN_ARGS: usize = 0;
    const MAX_ARGS: usize = usize::MAX;
}

impl<A: smallvec::Array> Format for SmallVec<A>
where
    A::Item: fmt::Debug + fmt::Display,
{
    type Inner = A::Item;

    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        mut fmt_inner: impl FnMut(&Self::Inner, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        let mut args = self.iter();
        if let Some(arg) = args.next() {
            fmt_inner(arg, f)?;
        }
        for arg in args {
            write!(f, " ")?;
            fmt_inner(arg, f)?;
        }
        Ok(())
    }
}

impl<'a, L: Logic> Iterate<'a, L> for Void {
    type Terms = slice::Iter<'a, Term<L>>;
    type IntoTerms = vec::IntoIter<Term<L>>;

    fn terms(&'a self) -> Self::Terms {
        match *self {}
    }
    fn into_terms(self) -> Self::IntoTerms {
        match self {}
    }
}

impl<'a, L: Logic> Arguments<'a, L> for Void {}

impl<'a, L: Logic> Iterate<'a, L> for UF<Term<L>> {
    type Terms = slice::Iter<'a, Term<L>>;
    type IntoTerms = vec::IntoIter<Term<L>>;

    fn terms(&'a self) -> Self::Terms {
        self.args.iter()
    }
    fn into_terms(self) -> Self::IntoTerms {
        Vec::from(self.args).into_iter()
    }
}

impl<'a, L: Logic> Arguments<'a, L> for UF<Term<L>> {}
