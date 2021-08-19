// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::{
    Command, Ctx, Fold, Folder, FunctionDec, IConst, ICoreOp, ILet, IMatch, IOp, IQuantifier,
    ISort, ISymbol, IVar, Logic, Numeral, SuperFold, Term, IUF,
};

#[doc(hidden)]
pub struct Marker;

/// An `IntraLogicFolder<T>` is a type that can be used to transform SMT terms within logic `T`.
/// This a more specialized version of [`Folder`] that can provide more default method
/// implementations and require specifying fewer associated types.
///
/// # Examples
///
/// ### Partially evaluating `not` operations
///
/// This is an equivalent folder to the one defined in the examples of [`Folder`], but is much less
/// verbose because it can take advantage of `IntraLogicFolder`'s default implementations.
///
/// ```
/// # fn main() {
/// use amzn_smt_ir::fold::{Fold, SuperFold, IntraLogicFolder};
/// use amzn_smt_ir::{CoreOp, ICoreOp, Term, Let, Match, Logic, Void};
///
/// struct PartiallyEvaluateNot;
///
/// impl<T: Logic> IntraLogicFolder<T> for PartiallyEvaluateNot {
///     type Error = ();
///
///     fn fold_core_op(&mut self, op: ICoreOp<T>) -> Result<Term<T>, Self::Error> {
///         // Recursively fold arguments, then check if there's a `not` we can evaluate
///         Ok(match op.super_fold_with(self)? {
///             CoreOp::Not(Term::CoreOp(op)) if matches!(*op, CoreOp::True) => false.into(),
///             CoreOp::Not(Term::CoreOp(op)) if matches!(*op, CoreOp::False) => true.into(),
///             op => op.into(),
///         })
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
pub trait IntraLogicFolder<T: Logic>: Sized {
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
    fn fold_term(&mut self, term: Term<T>) -> Result<Term<T>, Self::Error> {
        term.super_fold_with(self)
    }

    /// Transforms a constant.
    /// By default, returns the constant as-is.
    fn fold_const(&mut self, constant: IConst) -> Result<Term<T>, Self::Error> {
        Ok(constant.into())
    }

    /// Transforms a variable.
    /// By default, returns the variable as-is.
    fn fold_var(&mut self, var: IVar<T::Var>) -> Result<Term<T>, Self::Error> {
        Ok(var.into())
    }

    /// Transforms a Core operation, recursively transforming its arguments.
    /// By default, calls [`SuperFold::super_fold_with`].
    fn fold_core_op(&mut self, op: ICoreOp<T>) -> Result<Term<T>, Self::Error> {
        op.super_fold_with(self).map(Into::into)
    }

    /// Transforms a non-Core operation, recursively transforming its arguments.
    /// By default, calls [`SuperFold::super_fold_with`].
    fn fold_theory_op(&mut self, op: IOp<T>) -> Result<Term<T>, Self::Error> {
        op.super_fold_with(self).map(Into::into)
    }

    /// Transforms an uninterpreted function, recursively transforming its arguments.
    /// By default, calls [`SuperFold::super_fold_with`].
    fn fold_uninterpreted_func(&mut self, func: IUF<T>) -> Result<Term<T>, Self::Error> {
        func.super_fold_with(self).map(Into::into)
    }

    /// Transforms a let binder, recursively transforming its arguments.
    /// By default, calls [`SuperFold::super_fold_with`].
    fn fold_let(&mut self, l: ILet<T>) -> Result<Term<T>, Self::Error> {
        l.super_fold_with(self).map(Into::into)
    }

    /// Transforms a match binder, recursively transforming its arguments.
    /// By default, calls [`SuperFold::super_fold_with`].
    fn fold_match(&mut self, m: IMatch<T>) -> Result<Term<T>, Self::Error> {
        m.super_fold_with(self).map(Into::into)
    }

    /// Transforms a quantifier, recursively folding its arguments.
    /// By default, calls [`SuperFold::super_fold_with`].
    fn fold_quantifier(&mut self, quantifier: IQuantifier<T>) -> Result<Term<T>, Self::Error> {
        quantifier.super_fold_with(self).map(Into::into)
    }

    /// Transforms a set-logic command.
    /// By default, returns as-is.
    fn fold_set_logic(&mut self, logic: ISymbol) -> Result<Command<Term<T>>, Self::Error> {
        Ok(Command::SetLogic { symbol: logic })
    }

    /// Transforms an asserted term.
    /// By default, calls [`Self::fold_term`].
    fn fold_assert(&mut self, asserted: Term<T>) -> Result<Command<Term<T>>, Self::Error> {
        self.fold_term(asserted).map(Command::Assert)
    }

    /// Transforms a constant declaration.
    /// By default, returns as-is.
    fn fold_declare_const(
        &mut self,
        symbol: ISymbol,
        sort: ISort,
    ) -> Result<Command<Term<T>>, Self::Error> {
        Ok(Command::DeclareConst { symbol, sort })
    }

    /// Transforms a function declaration.
    /// By default, returns as-is.
    fn fold_declare_fun(
        &mut self,
        symbol: ISymbol,
        parameters: Vec<ISort>,
        sort: ISort,
    ) -> Result<Command<Term<T>>, Self::Error> {
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
    ) -> Result<Command<Term<T>>, Self::Error> {
        Ok(Command::DeclareSort { symbol, arity })
    }

    /// Transforms a function definition.
    /// By default, recursively transforms the function body with [`Self::fold_term`].
    fn fold_define_fun(
        &mut self,
        sig: FunctionDec,
        body: Term<T>,
    ) -> Result<Command<Term<T>>, Self::Error> {
        let term = body.fold_with(self)?;
        Ok(Command::DefineFun { sig, term })
    }

    /// Transforms a recursive function definition.
    /// By default, recursively transforms the function body with [`Self::fold_term`].
    fn fold_define_fun_rec(
        &mut self,
        sig: FunctionDec,
        body: Term<T>,
    ) -> Result<Command<Term<T>>, Self::Error> {
        let term = body.fold_with(self)?;
        Ok(Command::DefineFunRec { sig, term })
    }

    /// Transforms a set of recursive function definition.
    /// By default, recursively transforms each function body with [`Self::fold_term`].
    fn fold_define_funs_rec(
        &mut self,
        funs: Vec<(FunctionDec, Term<T>)>,
    ) -> Result<Command<Term<T>>, Self::Error> {
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
    ) -> Result<Command<Term<T>>, Self::Error> {
        Ok(Command::DefineSort {
            symbol,
            parameters,
            sort,
        })
    }

    /// Transforms a `get-value` call.
    /// By default, recursively transforms each term with [`Self::fold_term`].
    fn fold_get_value(&mut self, terms: Vec<Term<T>>) -> Result<Command<Term<T>>, Self::Error> {
        let terms = terms.fold_with(self)?;
        Ok(Command::GetValue { terms })
    }
}

impl<T: Logic, F: IntraLogicFolder<T>> Folder<T, Marker> for F {
    type Output = Term<T>;
    type Error = F::Error;

    fn context(&self) -> Option<&Ctx> {
        self.context()
    }

    fn context_mut(&mut self) -> Option<&mut Ctx> {
        self.context_mut()
    }

    fn fold_term(&mut self, term: Term<T>) -> Result<Self::Output, Self::Error> {
        self.fold_term(term)
    }

    fn fold_const(&mut self, constant: IConst) -> Result<Self::Output, Self::Error> {
        self.fold_const(constant)
    }

    fn fold_var(&mut self, var: IVar<T::Var>) -> Result<Self::Output, Self::Error> {
        self.fold_var(var)
    }

    fn fold_core_op(&mut self, op: ICoreOp<T>) -> Result<Self::Output, Self::Error> {
        self.fold_core_op(op)
    }

    fn fold_theory_op(&mut self, op: IOp<T>) -> Result<Self::Output, Self::Error> {
        self.fold_theory_op(op)
    }

    fn fold_uninterpreted_func(&mut self, func: IUF<T>) -> Result<Self::Output, Self::Error> {
        self.fold_uninterpreted_func(func)
    }

    fn fold_let(&mut self, l: ILet<T>) -> Result<Self::Output, Self::Error> {
        self.fold_let(l)
    }

    fn fold_match(&mut self, m: IMatch<T>) -> Result<Self::Output, Self::Error> {
        self.fold_match(m)
    }

    fn fold_quantifier(&mut self, quantifier: IQuantifier<T>) -> Result<Self::Output, Self::Error> {
        self.fold_quantifier(quantifier)
    }

    fn fold_set_logic(&mut self, logic: ISymbol) -> Result<Command<Self::Output>, Self::Error> {
        self.fold_set_logic(logic)
    }

    fn fold_assert(&mut self, asserted: Term<T>) -> Result<Command<Self::Output>, Self::Error> {
        self.fold_assert(asserted)
    }

    fn fold_declare_const(
        &mut self,
        symbol: ISymbol,
        sort: ISort,
    ) -> Result<Command<Self::Output>, Self::Error> {
        self.fold_declare_const(symbol, sort)
    }

    fn fold_declare_fun(
        &mut self,
        symbol: ISymbol,
        parameters: Vec<ISort>,
        sort: ISort,
    ) -> Result<Command<Self::Output>, Self::Error> {
        self.fold_declare_fun(symbol, parameters, sort)
    }

    fn fold_declare_sort(
        &mut self,
        symbol: ISymbol,
        arity: Numeral,
    ) -> Result<Command<Self::Output>, Self::Error> {
        self.fold_declare_sort(symbol, arity)
    }

    fn fold_define_fun(
        &mut self,
        sig: FunctionDec,
        body: Term<T>,
    ) -> Result<Command<Self::Output>, Self::Error> {
        self.fold_define_fun(sig, body)
    }

    fn fold_define_fun_rec(
        &mut self,
        sig: FunctionDec,
        body: Term<T>,
    ) -> Result<Command<Self::Output>, Self::Error> {
        self.fold_define_fun_rec(sig, body)
    }

    fn fold_define_funs_rec(
        &mut self,
        funs: Vec<(FunctionDec, Term<T>)>,
    ) -> Result<Command<Self::Output>, Self::Error> {
        self.fold_define_funs_rec(funs)
    }

    fn fold_define_sort(
        &mut self,
        symbol: ISymbol,
        parameters: Vec<ISymbol>,
        sort: ISort,
    ) -> Result<Command<Self::Output>, Self::Error> {
        self.fold_define_sort(symbol, parameters, sort)
    }

    fn fold_get_value(
        &mut self,
        terms: Vec<Term<T>>,
    ) -> Result<Command<Self::Output>, Self::Error> {
        self.fold_get_value(terms)
    }
}
