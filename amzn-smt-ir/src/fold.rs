//! Traits for transforming [`Term`]s into other terms.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    Command, CoreOp, Ctx, FunctionDec, IConst, ICoreOp, IIndex, ILet, IMatch, IOp, IQuantifier,
    ISort, ISymbol, IVar, Let, Logic, Quantifier, Sorted, Term, Void, IUF, UF,
};
pub use amzn_smt_ir_derive::Fold;

mod compose;
pub use compose::{Compose, TryComposed};
mod intra;
pub use intra::IntraLogicFolder;
mod inter;
pub use inter::InterLogicFolder;
use smallvec::SmallVec;
use smt2parser::Numeral;

/// A `Folder<T>` is a type that can be used to transform SMT terms in logic `T` to some other type.
/// For example, a folder could be used to partially evaluate a term or encode it into a simpler
/// logic (e.g. bit-blasting bit-vectors). Useful folders will often preserve equisatisfiability,
/// although this is not required.
///
/// **Note: When writing code generic over folders, be generic over `Folder<T, M>` instead of
/// `Folder<T>`, as the latter only includes types that directly implement `Folder`. See
/// [Emulating Specialization](#emulating-specialization) below for details.
///
/// [`Const`], [`Var`], [`CoreOp`], and [`Op`] implement [`Fold`]; when [`Fold::fold_with`] is called
/// with a folder, it will recursively fold all of the subexpressions contained within. For types
/// that have corresponding hooks in [`Folder`] (e.g. [`Folder::fold_var`], [`Folder::fold_core_op`]),
/// [`Fold::fold_with`] will call the hook, which should then recusively fold subexpressions -- this
/// can be accomplished through a call to [`SuperFold::super_fold_with`].
///
/// # Emulating specialization
///
/// The [`IntraLogicFolder`] and [`InterLogicFolder`] traits are more specialized versions of
/// [`Folder`], providing default implementations for more `fold_*` hooks where possible. These
/// traits implement `Folder` through a blanket impl, which would produce conflicting trait
/// impls because [specialization](https://rust-lang.github.io/rfcs/1210-impl-specialization.html)
/// is not implemented. To work around this until some form of specialization lands, `Folder` has
/// a parameter `M` that acts as a *marker* of which `Folder`-family trait was directly implemented.
/// Types that directly implement `Folder` have a marker of `()`, while types that indirectly
/// implement it through a more specialized trait use marker types corresponding to that trait.
/// This makes the blanket impls produce distinct implementations `Folder<_, A>`, `Folder<_, B>`, etc.
///
/// # Examples
///
/// ### Partially evaluating `not` operations
///
/// ```
/// # fn main() {
/// use amzn_smt_ir::fold::{Fold, Folder, SuperFold};
/// use amzn_smt_ir::{CoreOp, ICoreOp, IVar, IUF, IOp, Term, ILet, IMatch, Logic, Void, IConst, IQuantifier};
///
/// struct PartiallyEvaluateNot;
///
/// impl<T: Logic> Folder<T> for PartiallyEvaluateNot {
///     type Output = Term<T>;
///     type Error = ();
///
///     fn fold_const(&mut self, constant: IConst) -> Result<Self::Output, Self::Error> {
///         Ok(constant.into())
///     }
///
///     fn fold_var(&mut self, var: IVar<T::Var>) -> Result<Self::Output, Self::Error> {
///         Ok(var.into())
///     }
///
///     fn fold_core_op(&mut self, op: ICoreOp<T>) -> Result<Self::Output, Self::Error> {
///         // Recursively fold arguments, then check if there's a `not` we can evaluate
///         Ok(match op.super_fold_with(self)? {
///             CoreOp::Not(Term::CoreOp(op)) if matches!(*op, CoreOp::True) => false.into(),
///             CoreOp::Not(Term::CoreOp(op)) if matches!(*op, CoreOp::False) => true.into(),
///             op => op.into(),
///         })
///     }
///
///     fn fold_theory_op(&mut self, op: IOp<T>) -> Result<Self::Output, Self::Error> {
///         op.super_fold_with(self).map(Into::into)
///     }
///
///     fn fold_uninterpreted_func(&mut self, uf: IUF<T>) -> Result<Self::Output, Self::Error> {
///         uf.super_fold_with(self).map(Into::into)
///     }
///
///     fn fold_let(&mut self, l: ILet<T>) -> Result<Self::Output, Self::Error> {
///         l.super_fold_with(self).map(Into::into)
///     }
///
///     fn fold_match(&mut self, m: IMatch<T>) -> Result<Self::Output, Self::Error> {
///         m.super_fold_with(self).map(Into::into)
///     }
///
///     fn fold_quantifier(&mut self, quantifier: IQuantifier<T>) -> Result<Self::Output, Self::Error> {
///         quantifier.super_fold_with(self).map(Into::into)
///     }
/// }
///
/// let f1: Term = !Term::CoreOp(true.into());
/// let f2 = f1.clone() & !Term::CoreOp(false.into());
/// let mut folder = PartiallyEvaluateNot;
/// assert_eq!(f1.fold_with(&mut folder), Ok(false.into()));
/// assert_eq!(f2.fold_with(&mut folder), Ok(CoreOp::And([false.into(), true.into()].into()).into()));
/// # }
/// ```
pub trait Folder<T: Logic, M = ()>: Compose {
    /// Type produced by the transformation.
    /// If `Output = Term<T>`, implement [`IntraLogicFolder`] instead.
    /// If `Output = Term<U>` for some `U: Logic`, implement [`InterLogicFolder`] instead.
    type Output;

    /// Type of errors that the folder may run into.
    type Error;

    /// Gets the context tracked by the folder, if applicable.
    /// Tracking context enables things like determining the sorts of expressions and which
    /// variables are free/bound, but a folder that doesn't need that information can leave
    /// this method defaulted, which will return `None`.
    fn context(&self) -> Option<&Ctx> {
        None
    }

    /// Gets a mutable reference to the context tracked by the folder, if applicable.
    /// Tracking context enables things like determining the sorts of expressions and which
    /// variables are free/bound, but a folder that doesn't need that information can leave
    /// this method defaulted, which will return `None`.
    fn context_mut(&mut self) -> Option<&mut Ctx> {
        debug_assert!(
            self.context().is_none(),
            "context() and context_mut() should be implemented together"
        );
        None
    }

    /// Transforms a term, recursively transforming its contents.
    /// By default, calls [`SuperFold::super_fold_with`].
    fn fold_term(&mut self, term: Term<T>) -> Result<Self::Output, Self::Error> {
        term.super_fold_with(self)
    }

    /// Transforms a constant.
    fn fold_const(&mut self, constant: IConst) -> Result<Self::Output, Self::Error>;

    /// Transforms a variable.
    fn fold_var(&mut self, var: IVar<T::Var>) -> Result<Self::Output, Self::Error>;

    /// Transforms an SMT-LIB Core operation, recursively folding its arguments.
    fn fold_core_op(&mut self, op: ICoreOp<T>) -> Result<Self::Output, Self::Error>;

    /// Transforms a non-core operation, recursively folding its arguments.
    fn fold_theory_op(&mut self, op: IOp<T>) -> Result<Self::Output, Self::Error>;

    /// Transforms an uninterpreted function, recursively folding its arguments.
    fn fold_uninterpreted_func(&mut self, func: IUF<T>) -> Result<Self::Output, Self::Error>;

    /// Transforms a let binder, recursively folding its arguments.
    fn fold_let(&mut self, l: ILet<T>) -> Result<Self::Output, Self::Error>;

    /// Transforms a match binder, recursively folding its arguments.
    fn fold_match(&mut self, m: IMatch<T>) -> Result<Self::Output, Self::Error>;

    /// Transforms a quantifier, recursively folding its arguments.
    fn fold_quantifier(&mut self, quantifier: IQuantifier<T>) -> Result<Self::Output, Self::Error>;

    /// Transforms a set-logic command.
    /// By default, returns as-is.
    fn fold_set_logic(&mut self, logic: ISymbol) -> Result<Command<Self::Output>, Self::Error> {
        Ok(Command::SetLogic { symbol: logic })
    }

    /// Transforms an asserted term.
    /// By default, calls [`Self::fold_term`].
    fn fold_assert(&mut self, asserted: Term<T>) -> Result<Command<Self::Output>, Self::Error> {
        self.fold_term(asserted)
            .map(|term| Command::Assert { term })
    }

    /// Transforms a constant declaration.
    /// By default, returns as-is.
    fn fold_declare_const(
        &mut self,
        symbol: ISymbol,
        sort: ISort,
    ) -> Result<Command<Self::Output>, Self::Error> {
        Ok(Command::DeclareConst { symbol, sort })
    }

    /// Transforms a function declaration.
    /// By default, returns as-is.
    fn fold_declare_fun(
        &mut self,
        symbol: ISymbol,
        parameters: Vec<ISort>,
        sort: ISort,
    ) -> Result<Command<Self::Output>, Self::Error> {
        Ok(Command::DeclareFun {
            symbol,
            parameters,
            sort,
        })
    }

    /// Transforms a sort declaration.
    /// By default, returns as-is.
    fn fold_declare_sort(
        &mut self,
        symbol: ISymbol,
        arity: Numeral,
    ) -> Result<Command<Self::Output>, Self::Error> {
        Ok(Command::DeclareSort { symbol, arity })
    }

    /// Transforms a function definition.
    /// By default, recursively transforms the function body with [`Self::fold_term`].
    fn fold_define_fun(
        &mut self,
        sig: FunctionDec,
        body: Term<T>,
    ) -> Result<Command<Self::Output>, Self::Error> {
        let term = body.fold_with(self)?;
        Ok(Command::DefineFun { sig, term })
    }

    /// Transforms a recursive function definition.
    /// By default, recursively transforms the function body with [`Self::fold_term`].
    fn fold_define_fun_rec(
        &mut self,
        sig: FunctionDec,
        body: Term<T>,
    ) -> Result<Command<Self::Output>, Self::Error> {
        let term = body.fold_with(self)?;
        Ok(Command::DefineFunRec { sig, term })
    }

    /// Transforms a set of recursive function definition.
    /// By default, recursively transforms each function body with [`Self::fold_term`].
    fn fold_define_funs_rec(
        &mut self,
        funs: Vec<(FunctionDec, Term<T>)>,
    ) -> Result<Command<Self::Output>, Self::Error> {
        let funs = funs
            .into_iter()
            .map(|(sig, body)| Ok((sig, body.fold_with(self)?)))
            .collect::<Result<_, _>>()?;
        Ok(Command::DefineFunsRec { funs })
    }

    /// Transforms a sort definition.
    /// By default, returns as-is.
    fn fold_define_sort(
        &mut self,
        symbol: ISymbol,
        parameters: Vec<ISymbol>,
        sort: ISort,
    ) -> Result<Command<Self::Output>, Self::Error> {
        Ok(Command::DefineSort {
            symbol,
            parameters,
            sort,
        })
    }

    /// Transforms a `get-value` call.
    /// By default, recursively transforms each term with [`Self::fold_term`].
    fn fold_get_value(
        &mut self,
        terms: Vec<Term<T>>,
    ) -> Result<Command<Self::Output>, Self::Error> {
        let terms = terms.fold_with(self)?;
        Ok(Command::GetValue { terms })
    }
}

/// `Fold` implements the logic to recursively fold the contents of a type using a folder (see [`Folder`]).
/// This should usually not be implemented manually; in particular, types used as operations
/// (i.e. the `T::Op` of a `T: Logic`) should derive `Fold` using the [`Fold`] derive macro.
///
/// # Examples
///
/// ## Deriving `Fold` for a simple enum.
///
/// ```
/// # fn main() {
/// use amzn_smt_ir::{fold::Fold, Term, Logic, Operation};
///
/// #[derive(Operation, Fold)]
/// enum AddOrSubtract<Term> {
///     Add(Vec<Term>),
///     Subtract(Term, Term),
/// }
/// # }
/// ```
pub trait Fold<T: Logic, Out> {
    /// Type output by the transformation.
    type Output;

    /// Transforms `self` using `folder`.
    ///
    /// If type inference is failing because it can't figure out which `T` to use, use
    /// [`Logic::fold`] to resolve the ambiguity.
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>;
}

/// `SuperFold` implements the logic to recursively fold the contents of types that have hooks in
/// [`Folder`] using a folder (see [`Folder`]).
/// This should usually not be implemented manually; in particular, types used as operations
/// (i.e. the `T::Op` of a `T: Logic`) should derive [`SuperFold`] using the [`Fold`] derive macro.
pub trait SuperFold<T: Logic, Out> {
    /// Type output by the transformation, e.g. `Foo<Out>` for an implementation for `Foo<U: Fold<T, Out>>`.
    type Output;

    /// Recursively transforms the contents of `self` using `folder.`
    fn super_fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>;
}

impl<T: Logic, Out> Fold<T, Out> for Term<T> {
    type Output = Out;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        folder.fold_term(self)
    }
}

impl<T: Logic, Out> Fold<T, Out> for &Term<T> {
    type Output = Out;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        folder.fold_term(self.clone())
    }
}

impl<T: Logic, Out> SuperFold<T, Out> for Term<T> {
    type Output = Out;

    fn super_fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        match self {
            Self::Constant(c) => c.fold_with(folder),
            Self::Variable(v) => v.fold_with(folder),
            Self::CoreOp(op) => op.fold_with(folder),
            Self::OtherOp(op) => op.fold_with(folder),
            Self::UF(uf) => uf.fold_with(folder),
            Self::Let(l) => l.fold_with(folder),
            Self::Match(m) => m.fold_with(folder),
            Self::Quantifier(q) => q.fold_with(folder),
        }
    }
}

impl<T: Logic, Out> SuperFold<T, Out> for &Term<T> {
    type Output = Out;

    fn super_fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        self.clone().super_fold_with(folder)
    }
}

impl<T: Logic, Out> Fold<T, Out> for IConst {
    type Output = Out;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        folder.fold_const(self)
    }
}

impl<T: Logic, Out> Fold<T, Out> for IVar<T::Var> {
    type Output = Out;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        folder.fold_var(self)
    }
}

// TODO: extend `Fold` derive to work for `CoreOp`
impl<T: Logic, Out> Fold<T, Out> for ICoreOp<T> {
    type Output = Out;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        folder.fold_core_op(self)
    }
}

// TODO: extend `Fold` derive to work for `CoreOp`
impl<T: Logic, Inner: Fold<T, Out>, Out> SuperFold<T, Out> for CoreOp<Inner> {
    type Output = CoreOp<Inner::Output>;
    fn super_fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        use CoreOp::*;
        const STACK_RED_ZONE: usize = 32 * 1024;
        const NEW_STACK_SIZE: usize = 1024 * 1024;
        let op = match self {
            True => True,
            False => False,
            Not(t) => Not(t.fold_with(folder)?),
            And(args) => And(stacker::maybe_grow(STACK_RED_ZONE, NEW_STACK_SIZE, || {
                args.fold_with(folder)
            })?),
            Or(args) => Or(stacker::maybe_grow(STACK_RED_ZONE, NEW_STACK_SIZE, || {
                args.fold_with(folder)
            })?),
            Xor(args) => Xor(args.fold_with(folder)?),
            Imp(args) => Imp(args.fold_with(folder)?),
            Eq(args) => Eq(args.fold_with(folder)?),
            Distinct(args) => Distinct(args.fold_with(folder)?),
            Ite(i, t, e) => Ite(
                i.fold_with(folder)?,
                t.fold_with(folder)?,
                e.fold_with(folder)?,
            ),
        };
        Ok(op)
    }
}

impl<L: Logic, Out> Fold<L, Out> for IOp<L> {
    type Output = Out;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<L, M, Output = Out>,
    {
        folder.fold_theory_op(self)
    }
}

impl<T: Logic, Out> Fold<T, Out> for IUF<T> {
    type Output = Out;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        folder.fold_uninterpreted_func(self)
    }
}

impl<T: Logic, Inner, Out> SuperFold<T, Out> for UF<Inner>
where
    Inner: Fold<T, Out>,
{
    type Output = UF<Inner::Output>;
    fn super_fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        let (func, args) = (self.func.fold_with(folder)?, self.args.fold_with(folder)?);
        Ok(UF { func, args })
    }
}

impl<T: Logic, Out> Fold<T, Out> for IQuantifier<T> {
    type Output = Out;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        folder.fold_quantifier(self)
    }
}

impl<T: Logic, Inner, Out> SuperFold<T, Out> for Quantifier<Inner>
where
    Inner: Fold<T, Out>,
{
    type Output = Quantifier<Inner::Output>;
    fn super_fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        use Quantifier::*;
        Ok(match self {
            Forall(vars, t) => Forall(vars.fold_with(folder)?, t.fold_with(folder)?),
            Exists(vars, t) => Exists(vars.fold_with(folder)?, t.fold_with(folder)?),
        })
    }
}

impl<T: Logic, Out> Fold<T, Out> for ILet<T> {
    type Output = Out;

    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        let old_bindings = if let Some(ctx) = folder.context_mut() {
            self.bindings
                .iter()
                .map(|(sym, t)| {
                    let sort = t.sort(ctx).ok();
                    let old_sort = ctx.local.bind_var(sym.clone(), sort);
                    (sym.clone(), old_sort)
                })
                .collect()
        } else {
            vec![]
        };
        let res = folder.fold_let(self);
        if let Some(ctx) = folder.context_mut() {
            for (sym, old_sort) in old_bindings {
                match old_sort {
                    None => ctx.local.unbind_var(&sym),
                    Some(sort) => {
                        ctx.local.bind_var(sym, sort);
                    }
                }
            }
        }
        res
    }
}

impl<T: Logic, Inner: Fold<T, Out>, Out> SuperFold<T, Out> for Let<Inner> {
    type Output = Let<Inner::Output>;

    fn super_fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        Ok(Let {
            bindings: self.bindings.fold_with(folder)?,
            term: self.term.fold_with(folder)?,
        })
    }
}

impl<T: Logic, Out> Fold<T, Out> for Void {
    type Output = Out;
    fn fold_with<F: Folder<T, M>, M>(self, _folder: &mut F) -> Result<Self::Output, F::Error> {
        match self {}
    }
}

impl<T: Logic, Out> SuperFold<T, Out> for Void {
    type Output = Void;
    fn super_fold_with<F: Folder<T, M>, M>(
        self,
        _folder: &mut F,
    ) -> Result<Self::Output, F::Error> {
        match self {}
    }
}

impl<T: Logic, Out> Fold<T, Out> for ISymbol {
    type Output = Self;
    fn fold_with<F, M>(self, _: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        Ok(self)
    }
}

impl<T: Logic, Out> Fold<T, Out> for ISort {
    type Output = Self;
    fn fold_with<F, M>(self, _: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        Ok(self)
    }
}

impl<T: Logic, Out, Inner: Fold<T, Out>> Fold<T, Out> for Vec<Inner> {
    type Output = Vec<<Inner as Fold<T, Out>>::Output>;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        self.into_iter().map(|t| t.fold_with(folder)).collect()
    }
}

impl<T: Logic, Out, Inner: Fold<T, Out>, const N: usize> Fold<T, Out> for SmallVec<[Inner; N]>
where
    [Inner; N]: smallvec::Array<Item = Inner>,
    [Inner::Output; N]: smallvec::Array<Item = Inner::Output>,
{
    type Output = SmallVec<[Inner::Output; N]>;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        self.into_iter().map(|t| t.fold_with(folder)).collect()
    }
}

impl<'a, T: Logic, Out, Inner, Output, const N: usize> Fold<T, Out> for &'a SmallVec<[Inner; N]>
where
    &'a Inner: Fold<T, Out, Output = Output>,
    [Inner; N]: smallvec::Array<Item = Inner>,
    [Output; N]: smallvec::Array<Item = Output>,
{
    type Output = SmallVec<[Output; N]>;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        self.iter().map(|t| t.fold_with(folder)).collect()
    }
}

impl<T: Logic, Out, Inner: Fold<T, Out>> Fold<T, Out> for Box<[Inner]> {
    type Output = Box<[<Inner as Fold<T, Out>>::Output]>;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        self.into_vec()
            .into_iter()
            .map(|t| t.fold_with(folder))
            .collect()
    }
}

impl<T: Logic, Out, const N: usize> Fold<T, Out> for [IIndex; N] {
    type Output = Self;
    fn fold_with<F, M>(self, _: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        Ok(self)
    }
}

impl<T: Logic, Out, Inner, Output> Fold<T, Out> for &[Inner]
where
    for<'a> &'a Inner: Fold<T, Out, Output = Output>,
{
    type Output = Vec<Output>;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        self.iter().map(|t| t.fold_with(folder)).collect()
    }
}

impl<T: Logic, Out, Inner, Output> Fold<T, Out> for &Vec<Inner>
where
    for<'a> &'a Inner: Fold<T, Out, Output = Output>,
{
    type Output = Vec<Output>;
    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<T, M, Output = Out>,
    {
        self.iter().map(|t| t.fold_with(folder)).collect()
    }
}

macro_rules! impl_fold_tuple {
    ($($x:ident),*) => {
        impl<T: Logic, Out, $($x),*> Fold<T, Out> for ($($x),*)
        where
            $($x: Fold<T, Out>),*
        {
            type Output = ($($x::Output),*);
            fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
            where
                F: Folder<T, M, Output = Out>,
            {
                #[allow(non_snake_case)]
                let ($($x),*) = self;
                Ok(($($x.fold_with(folder)?),*))
            }
        }
    };
}

impl_fold_tuple!(A, B);
impl_fold_tuple!(A, B, C);
impl_fold_tuple!(A, B, C, D);
impl_fold_tuple!(A, B, C, D, E);

impl<L: Logic, Out> Fold<L, Out> for Command<Term<L>> {
    type Output = Command<Out>;

    fn fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
    where
        F: Folder<L, M, Output = Out>,
    {
        use smt2parser::concrete::Command::*;
        if let Some(ctx) = folder.context_mut() {
            ctx.process(&self);
        }
        let command = match self {
            Assert { term } => folder.fold_assert(term)?,
            CheckSat => CheckSat,
            CheckSatAssuming { literals } => CheckSatAssuming { literals },
            DeclareConst { symbol, sort } => folder.fold_declare_const(symbol, sort)?,
            DeclareDatatype { symbol, datatype } => DeclareDatatype { symbol, datatype },
            DeclareDatatypes { datatypes } => DeclareDatatypes { datatypes },
            DeclareFun {
                symbol,
                parameters,
                sort,
            } => folder.fold_declare_fun(symbol, parameters, sort)?,
            DeclareSort { symbol, arity } => folder.fold_declare_sort(symbol, arity)?,
            DefineFun { sig, term } => folder.fold_define_fun(sig, term)?,
            DefineFunRec { sig, term } => folder.fold_define_fun_rec(sig, term)?,
            DefineFunsRec { funs } => folder.fold_define_funs_rec(funs)?,
            DefineSort {
                symbol,
                parameters,
                sort,
            } => folder.fold_define_sort(symbol, parameters, sort)?,
            Echo { message } => Echo { message },
            Exit => Exit,
            GetAssertions => GetAssertions,
            GetAssignment => GetAssignment,
            GetInfo { flag } => GetInfo { flag },
            GetModel => GetModel,
            GetOption { keyword } => GetOption { keyword },
            GetProof => GetProof,
            GetUnsatAssumptions => GetUnsatAssumptions,
            GetUnsatCore => GetUnsatCore,
            GetValue { terms } => folder.fold_get_value(terms)?,
            Pop { level } => Pop { level },
            Push { level } => Push { level },
            Reset => Reset,
            ResetAssertions => ResetAssertions,
            SetInfo { keyword, value } => SetInfo { keyword, value },
            SetLogic { symbol } => folder.fold_set_logic(symbol)?,
            SetOption { keyword, value } => SetOption { keyword, value },
        };
        if let Some(ctx) = folder.context_mut() {
            ctx.process(&command);
        }
        Ok(command)
    }
}
