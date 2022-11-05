//! Representations of SMT-LIB logics.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    fold::{Fold, Folder, SuperFold},
    quantifier::Quantifier,
    uf::UninterpretedFunction,
    visit::SuperVisit,
    Arguments, IOp, IQuantifier, Internable, Operation, Sorted, Term, IUF,
};
use std::{
    fmt::{Debug, Display},
    hash::Hash,
};

/// An SMT logic with variables of type [`Self::Var`],
/// operations of type [`Self::Op`], and quantifiers of type [`Self::Quantifier`].
///
/// [`Op`](Self::Op) always includes the operations in SMT-LIB's Core theory (`and`, `or`, `not`,
/// etc.) so an implementation of [`Logic`] that doesn't need any extra operators can specify an
/// uninhabited type for [`Self::Op`]. ([`Void`](crate::Void) is provided for this purpose.

/// # Examples
///
/// ## Basic arithmetic
///
/// The following logic extends the core theory with integer constants and variables, unary
/// negation, binary subtraction, and variadic addition.
///
/// ```
/// # fn main() {
/// use amzn_smt_ir::{fold::Fold, visit::Visit, *};
///
/// #[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
/// struct BasicArith;
///
/// #[derive(Clone, Operation, Fold, Visit, Hash, PartialEq, Eq)]
/// enum Op<Term> {
///     Negative(Term),
///     Minus(Term, Term),
///     Plus(Vec<Term>),
/// }
///
/// impl<L: Logic> Sorted<L> for Op<Term<L>> {
///     fn sort(&self, _: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
///         Ok(ISort::int())
///     }
/// }
///
/// impl Logic for BasicArith {
///     type Var = QualIdentifier;
///     type Op = Op<Term<Self>>;
///     type Quantifier = Void;
///     type UninterpretedFunc = Void;
/// }
/// # }
/// ```
pub trait Logic: Clone + Debug + Default + Hash + PartialEq + Eq + 'static {
    /// Type of variables in the logic.
    type Var: Internable + Sorted<Self> + Clone + Debug + Display;

    /// Type of non-core operations in the logic.
    ///
    /// Operations in the SMT-LIB Core theory are represented by [`CoreOp`](crate::CoreOp) and
    /// are implicitly included in every logic.
    type Op: Internable
        + Operation<Self>
        + Sorted<Self>
        + for<'a> Arguments<'a, Self>
        + Into<Term<Self>>
        + Into<IOp<Self>>
        + SuperFold<Self, Term<Self>, Output = Self::Op>
        + SuperVisit<Self>
        + Clone
        + Debug
        + Display;

    /// Type of quantifiers in the logic -- either [`Void`](crate::Void) for a quantifier-free logic or
    /// [`Quantifier`](crate::Quantifier) for a quantified logic.
    type Quantifier: Internable
        + Quantifier<Self>
        + Sorted<Self>
        + Into<Term<Self>>
        + Into<IQuantifier<Self>>
        + SuperFold<Self, Term<Self>, Output = Self::Quantifier>
        + SuperVisit<Self>
        + Clone
        + Debug
        + Display;

    /// Type of uninterpreted functions in the logic -- either [`Void`](crate::Void) for a logic without
    /// uninterpreted functions or [`UF`](crate::UF) for a logic containing them.
    type UninterpretedFunc: Internable
        + UninterpretedFunction<Self>
        + for<'a> Arguments<'a, Self>
        + Into<Term<Self>>
        + Into<IUF<Self>>
        + SuperFold<Self, Term<Self>, Output = Self::UninterpretedFunc>
        + SuperVisit<Self>
        + Clone
        + Debug
        + Display;

    /// Folds `x` with `folder`. Useful when the logic type can't be inferred by [`Fold::fold_with`].
    fn fold<F: Folder<Self, M>, Output, M>(
        x: impl Fold<Self, F::Output, Output = Output>,
        folder: &mut F,
    ) -> Result<Output, F::Error> {
        x.fold_with(folder)
    }
}

macro_rules! combine_ops {
    (pub enum $name:ident<Term> { $($variant:ident($inner:ident<Term>),)+ }) => {
        use crate::{args::Iterate, fold::{Folder, SuperFold}, visit::*, *};
        use std::fmt;

        #[derive(Clone, PartialEq, Eq, Hash)]
        pub enum $name<Term> {
            $($variant($inner<Term>)),*
        }

        impl<Term> fmt::Debug for $name<Term>
        where
            $($inner<Term>: fmt::Debug),*
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    $(Self::$variant(x) => x.fmt(f),)*
                }
            }
        }

        impl<Term> fmt::Display for $name<Term>
        where
            $($inner<Term>: fmt::Display),*
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    $(Self::$variant(x) => x.fmt(f),)*
                }
            }
        }

        impl<L: Logic, Term> Operation<L> for $name<Term>
        where
            $($inner<Term>: Operation<L>),*
        {
            fn parse(func: QualIdentifier, args: Vec<$crate::Term<L>>) -> Result<Self, InvalidOp<L>> {
                Err(InvalidOp { func, args })
                    $(.or_else(|InvalidOp { func, args }| Operation::parse(func, args).map(Self::$variant)))*
            }

            fn func(&self) -> ISymbol {
                match self {
                    $(Self::$variant(x) => x.func(),)*
                }
            }
        }

        impl<L: Logic, Term> SuperVisit<L> for $name<Term>
        where
            $($inner<Term>: SuperVisit<L>),*
        {
            fn super_visit_with<V: Visitor<L>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
                match self {
                    $(Self::$variant(x) => x.super_visit_with(visitor),)*
                }
            }
        }

        impl<L: Logic, Term, Out> SuperFold<L, Out> for $name<Term>
        where
            $($inner<Term>: SuperFold<L, Out, Output = $inner<Out>>),*
        {
            type Output = $name<Out>;

            fn super_fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
            where
                F: Folder<L, M, Output = Out>,
            {
                match self {
                    $(Self::$variant(x) => Ok($name::$variant(x.super_fold_with(folder)?)),)*
                }
            }
        }

        impl<L: Logic, Term> Sorted<L> for $name<Term>
        where
            $($inner<Term>: Sorted<L>),*
        {
            fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<$crate::Term<L>>> {
                match self {
                    $(Self::$variant(x) => x.sort(ctx),)*
                }
            }
        }

        impl<'a, L: Logic, Term> Iterate<'a, L> for $name<Term>
        where
            $($inner<Term>: Iterate<'a, L>),*
        {
            // TODO: generate an enum of each variant's iterator types instead of boxing
            type Terms = Box<dyn Iterator<Item = &'a $crate::Term<L>> + 'a>;
            type IntoTerms = Box<dyn Iterator<Item = $crate::Term<L>> + 'a>;

            fn terms(&'a self) -> Self::Terms {
                match self {
                    $(Self::$variant(x) => Box::new(x.terms()),)*
                }
            }
            fn into_terms(self) -> Self::IntoTerms {
                match self {
                    $(Self::$variant(x) => Box::new(x.into_terms()),)*
                }
            }
        }

        impl<'a, L: Logic> Arguments<'a, L> for $name<Term<L>> {}

        impl<L: Logic<Op = $name<Term>>, Term> From<$name<Term>> for IOp<L> {
            fn from(op: $name<Term>) -> Self {
                IOp::new(op)
            }
        }

        impl<L: Logic<Op = $name<Term>>, Term> From<$name<Term>> for $crate::Term<L> {
            fn from(op: $name<Term>) -> Self {
                Self::from(IOp::from(op))
            }
        }

        $(
            impl<Term> From<$inner<Term>> for $name<Term> {
                fn from(op: $inner<Term>) -> Self {
                    Self::$variant(op)
                }
            }
        )*
    };
}

pub mod all;
pub use all::ALL;
pub mod arrays;
pub use arrays::*;
pub mod bitvecs;
pub use bitvecs::*;
pub mod arith;
pub use arith::*;
pub mod strings;
pub use strings::*;
pub mod cvc5_sets;
pub use cvc5_sets::*;
