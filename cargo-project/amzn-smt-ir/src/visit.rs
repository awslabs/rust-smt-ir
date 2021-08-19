//! Traits for visiting [`Term`]s.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    script::Ctx, CoreOp, IConst, ICoreOp, IIndex, ILet, IMatch, IOp, IQuantifier, ISort, ISymbol,
    IVar, Index, Let, Logic, Match, Quantifier, Sorted, Term, Void, IUF, UF,
};
pub use amzn_smt_ir_derive::Visit;

mod control_flow;
pub use control_flow::ControlFlow;
use smallvec::SmallVec;

/// Unwraps a `ControlFlow` or propagates its `Break` value.
/// This replaces the `Try` implementation that would be used
/// with [`std::ops::ControlFlow`].
#[macro_export]
macro_rules! try_break {
    ($expr:expr) => {
        match $expr {
            $crate::visit::ControlFlow::Continue(c) => c,
            $crate::visit::ControlFlow::Break(b) => return $crate::visit::ControlFlow::Break(b),
        }
    };
}

/// A `Visitor` recursively traverses terms to compute some result.
///
/// [`Const`], [`Var`], [`CoreOp`], and [`Op`] implement [`Visit`]; when [`Visit::visit_with`] is
/// called with a visitor, it will recursively visit all of the subexpressions contained within.
/// For types that have corresponding hooks in [`Visitor`] (e.g. [`Visitor::visit_var`],
/// [`Visitor::visit_core_op`]), [`Visit::visit_with`] will call the hook, which should then
/// recusively visit subexpressions -- this can be accomplished through a call to
/// [`SuperVisit::super_visit_with`].
///
/// # Examples
///
/// ## Counting the number of `and`s
///
/// ```
/// # fn main() {
/// use amzn_smt_ir::{visit::{SuperVisit, Visit, Visitor, ControlFlow}, CoreOp, Term, ICoreOp, Logic};
///
/// #[derive(Default)]
/// struct AndCounter(usize);
///
/// impl<T: Logic> Visitor<T> for AndCounter {
///     type BreakTy = ();
///
///     fn visit_core_op(&mut self, op: &ICoreOp<T>) -> ControlFlow<Self::BreakTy> {
///         if let CoreOp::And(..) = op.as_ref() {
///             self.0 += 1;
///         }
///         op.super_visit_with(self)
///     }
/// }
///
/// let a: Term = Term::Variable("x".into());
/// let b = Term::Variable("y".into());
/// let c = false.into();
/// let f = (a & b.clone()) | (b & c);
///
/// let mut counter = AndCounter::default();
/// assert_eq!(f.visit_with(&mut counter), ControlFlow::CONTINUE);
/// assert_eq!(counter.0, 2);
/// # }
/// ```
///
/// ## Returning early
///
/// To end the traversal early, a visitor can return [`ControlFlow::Break`] from one of its visit
/// methods. The following visitor will recursively traverse terms until it finds a constant,
/// at which point it breaks with the value of the constant.
///
/// ```
/// # fn main() {
/// use amzn_smt_ir::{visit::{Visit, Visitor, ControlFlow}, *};
///
/// struct ConstantFinder;
///
/// impl<T: Logic> Visitor<T> for ConstantFinder {
///     type BreakTy = IConst;
///
///     fn visit_const(&mut self, constant: &IConst) -> ControlFlow<Self::BreakTy> {
///         ControlFlow::Break(constant.clone())
///     }
/// }
///
/// let x = IConst::from(Constant::Numeral(0u8.into()));
/// let f: Term = Term::Variable("x".into()) & x.clone().into();
/// assert_eq!(f.visit_with(&mut ConstantFinder), ControlFlow::Break(x));
/// # }
/// ```
pub trait Visitor<T: Logic>: Sized {
    /// The "break type" of the visitor, often `()`. It represents the result
    /// the visitor yields when it stops visiting early.
    type BreakTy;

    /// Gets the context tracked by the visitor, if applicable.
    /// Tracking context enables things like determining the sorts of expressions and which
    /// variables are free/bound, but a visitor that doesn't need that information can leave
    /// this method defaulted, which will return `None`.
    fn context(&self) -> Option<&Ctx> {
        None
    }

    /// Gets a mutable reference to the context tracked by the visitor, if applicable.
    /// Tracking context enables things like determining the sorts of expressions and which
    /// variables are free/bound, but a visitor that doesn't need that information can leave
    /// this method defaulted, which will return `None`.
    fn context_mut(&mut self) -> Option<&mut Ctx> {
        debug_assert!(
            self.context().is_none(),
            "context() and context_mut() should be implemented together"
        );
        None
    }

    /// Invoked for every term. By default, recursively visits the term's contents.
    fn visit_term(&mut self, term: &Term<T>) -> ControlFlow<Self::BreakTy> {
        term.super_visit_with(self)
    }

    /// Invoked for every constant. By default, does nothing and continues the traversal.
    fn visit_const(&mut self, _constant: &IConst) -> ControlFlow<Self::BreakTy> {
        ControlFlow::CONTINUE
    }

    /// Invoked for every variable. By default, does nothing and continues the traversal.
    fn visit_var(&mut self, _var: &IVar<T::Var>) -> ControlFlow<Self::BreakTy> {
        ControlFlow::CONTINUE
    }

    /// Invoked for every Core operation. By default, recursively visits the operation's arguments.
    fn visit_core_op(&mut self, op: &ICoreOp<T>) -> ControlFlow<Self::BreakTy> {
        op.super_visit_with(self)
    }

    /// Invoked for every non-Core operation in `T`. By default, recursively visits the operation's
    /// arguments.
    fn visit_theory_op(&mut self, op: &IOp<T>) -> ControlFlow<Self::BreakTy> {
        op.super_visit_with(self)
    }

    /// Invoked for every uninterpreted function in `T`. By default, recursively visits the
    /// function's arguments.
    fn visit_uninterpreted_func(&mut self, uf: &IUF<T>) -> ControlFlow<Self::BreakTy> {
        uf.super_visit_with(self)
    }

    /// Invoked for every let binder. By default, recursively visits the binder's arguments.
    fn visit_let(&mut self, l: &ILet<T>) -> ControlFlow<Self::BreakTy> {
        l.super_visit_with(self)
    }

    /// Invoked for every match binder. By default, recursively visits the binder's arguments.
    fn visit_match(&mut self, m: &IMatch<T>) -> ControlFlow<Self::BreakTy> {
        m.super_visit_with(self)
    }

    /// Invoked for every quantifier. By default, recursively visits the quantifier's arguments.
    fn visit_quantifier(&mut self, quantifier: &IQuantifier<T>) -> ControlFlow<Self::BreakTy> {
        quantifier.super_visit_with(self)
    }
}

/// `Visit` defines how a type is visited by a [`Visitor`].
/// This should usually not be implemented manually; in particular, types used as operations
/// (i.e. the `T::Op` of a `T: Logic`) should derive `Visit` using the [`Visit`] derive macro.
///
/// # Examples
///
/// ## Deriving `Visit` for a simple enum.
///
/// ```
/// # fn main() {
/// use amzn_smt_ir::{visit::Visit, Term, Logic};
///
/// #[derive(Visit)]
/// enum AddOrSubtract<Term> {
///     Add(Vec<Term>),
///     Subtract(Term, Term),
/// }
/// # }
/// ```
pub trait Visit<T: Logic> {
    /// Visits `self` with `visitor`.
    #[must_use]
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy>;
}

/// For types where [`Visit`] invokes a callback on the [`Visitor`], `SuperVisit` captures the
/// recursive behavior that visits all the contents of the type.
/// This should usually not be implemented manually; in particular, types used as operations
/// (i.e. the `T::Op` of a `T: Logic`) should derive `SuperVisit` using the [`Visit`] derive macro.
pub trait SuperVisit<T: Logic> {
    /// Recursively visits the contents of `self`.
    #[must_use]
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy>;
}

impl<T: Logic, V: Visitor<T>> Visitor<T> for &mut V {
    type BreakTy = V::BreakTy;
    fn visit_term(&mut self, term: &Term<T>) -> ControlFlow<Self::BreakTy> {
        (*self).visit_term(term)
    }
    fn visit_const(&mut self, constant: &IConst) -> ControlFlow<Self::BreakTy> {
        (*self).visit_const(constant)
    }
    fn visit_var(&mut self, var: &IVar<T::Var>) -> ControlFlow<Self::BreakTy> {
        (*self).visit_var(var)
    }
    fn visit_core_op(&mut self, op: &ICoreOp<T>) -> ControlFlow<Self::BreakTy> {
        (*self).visit_core_op(op)
    }
    fn visit_theory_op(&mut self, op: &IOp<T>) -> ControlFlow<Self::BreakTy> {
        (*self).visit_theory_op(op)
    }
    fn visit_let(&mut self, l: &ILet<T>) -> ControlFlow<Self::BreakTy> {
        (*self).visit_let(l)
    }
    fn visit_match(&mut self, m: &IMatch<T>) -> ControlFlow<Self::BreakTy> {
        (*self).visit_match(m)
    }
    fn visit_quantifier(&mut self, quantifier: &IQuantifier<T>) -> ControlFlow<Self::BreakTy> {
        (*self).visit_quantifier(quantifier)
    }
}

impl<T: Logic> Visit<T> for Term<T> {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_term(self)
    }
}

impl<T: Logic> SuperVisit<T> for Term<T> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            Self::Constant(c) => c.visit_with(visitor),
            Self::Variable(v) => v.visit_with(visitor),
            Self::CoreOp(op) => op.visit_with(visitor),
            Self::OtherOp(op) => op.visit_with(visitor),
            Self::UF(uf) => uf.visit_with(visitor),
            Self::Let(l) => l.visit_with(visitor),
            Self::Match(m) => m.visit_with(visitor),
            Self::Quantifier(q) => q.visit_with(visitor),
        }
    }
}

impl<T: Logic> Visit<T> for IConst {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_const(self)
    }
}

impl<T: Logic> Visit<T> for IVar<T::Var> {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_var(self)
    }
}

// TODO: extend `Visit` derive to work for `CoreOp`
impl<T: Logic> Visit<T> for ICoreOp<T> {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_core_op(self)
    }
}

// TODO: extend `Visit` derive to work for `CoreOp`
impl<T: Logic> SuperVisit<T> for CoreOp<Term<T>> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        use CoreOp::*;
        match self {
            True | False => ControlFlow::CONTINUE,
            Not(t) => t.visit_with(visitor),
            And(args) => args.visit_with(visitor),
            Or(args) => args.visit_with(visitor),
            Xor(args) => args.visit_with(visitor),
            Imp(args) => args.visit_with(visitor),
            Eq(args) => args.visit_with(visitor),
            Distinct(args) => args.visit_with(visitor),
            Ite(i, t, e) => {
                try_break!(i.visit_with(visitor));
                try_break!(t.visit_with(visitor));
                e.visit_with(visitor)
            }
        }
    }
}

impl<T: Logic> Visit<T> for IOp<T> {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_theory_op(self)
    }
}

impl<T: Logic> Visit<T> for IUF<T> {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_uninterpreted_func(self)
    }
}

impl<T: Logic<UninterpretedFunc = Self>, Inner: Visit<T>> SuperVisit<T> for UF<Inner> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        try_break!(self.func.visit_with(visitor));
        self.args.visit_with(visitor)
    }
}

impl<T: Logic> Visit<T> for IQuantifier<T> {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_quantifier(self)
    }
}

impl<T: Logic<Quantifier = Self>, Inner: Visit<T>> SuperVisit<T> for Quantifier<Inner> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            Self::Forall(vars, t) | Self::Exists(vars, t) => {
                try_break!(vars.visit_with(visitor));
                t.visit_with(visitor)
            }
        }
    }
}

impl<T: Logic> Visit<T> for ILet<T> {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        let old_bindings = if let Some(ctx) = visitor.context_mut() {
            self.bindings
                .iter()
                .map(|(sym, t)| {
                    let sort = t.sort(ctx).ok();
                    let old_sort = ctx.local.bind_var(sym.clone(), sort);
                    (sym, old_sort)
                })
                .collect()
        } else {
            vec![]
        };
        let res = visitor.visit_let(self);
        if let Some(ctx) = visitor.context_mut() {
            for (sym, old_sort) in old_bindings {
                match old_sort {
                    None => ctx.local.unbind_var(&sym),
                    Some(sort) => {
                        ctx.local.bind_var(sym.clone(), sort);
                    }
                }
            }
        }
        res
    }
}

impl<T: Logic> SuperVisit<T> for Let<Term<T>> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        let Let { bindings, term } = self;
        try_break!(bindings.visit_with(visitor));
        term.visit_with(visitor)
    }
}

impl<T: Logic> Visit<T> for IMatch<T> {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_match(self)
    }
}

impl<T: Logic> SuperVisit<T> for Match<Term<T>> {
    fn super_visit_with<V: Visitor<T>>(&self, _: &mut V) -> ControlFlow<V::BreakTy> {
        unimplemented!("match is currently unsupported")
    }
}

impl<T: Logic> Visit<T> for Void {
    fn visit_with<V: Visitor<T>>(&self, _visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match *self {}
    }
}

impl<T: Logic> SuperVisit<T> for Void {
    fn super_visit_with<V: Visitor<T>>(&self, _visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match *self {}
    }
}

impl<T: Logic> Visit<T> for ISymbol {
    fn visit_with<V: Visitor<T>>(&self, _: &mut V) -> ControlFlow<V::BreakTy> {
        ControlFlow::CONTINUE
    }
}

impl<T: Logic> Visit<T> for Index {
    fn visit_with<V: Visitor<T>>(&self, _: &mut V) -> ControlFlow<V::BreakTy> {
        ControlFlow::CONTINUE
    }
}

impl<T: Logic> Visit<T> for IIndex {
    fn visit_with<V: Visitor<T>>(&self, _: &mut V) -> ControlFlow<V::BreakTy> {
        ControlFlow::CONTINUE
    }
}

impl<T: Logic> Visit<T> for ISort {
    fn visit_with<V: Visitor<T>>(&self, _: &mut V) -> ControlFlow<V::BreakTy> {
        ControlFlow::CONTINUE
    }
}

impl<T: Logic, Inner: Visit<T>> Visit<T> for &Inner {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        (*self).visit_with(visitor)
    }
}

impl<T: Logic, Inner: Visit<T>> Visit<T> for Box<Inner> {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.as_ref().visit_with(visitor)
    }
}

/// Convenience function to visit all the items in an iterator.
pub fn visit_iter<T: Logic, Item: Visit<T>, B, V: Visitor<T, BreakTy = B>>(
    iter: impl Iterator<Item = Item>,
    visitor: &mut V,
) -> ControlFlow<B> {
    for elt in iter {
        try_break!(elt.visit_with(visitor));
    }
    ControlFlow::CONTINUE
}

impl<T: Logic, Inner: Visit<T>> Visit<T> for Vec<Inner> {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visit_iter(self.iter(), visitor)
    }
}

impl<T: Logic, A> Visit<T> for SmallVec<A>
where
    A: smallvec::Array,
    A::Item: Visit<T>,
{
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visit_iter(self.iter(), visitor)
    }
}

impl<T: Logic, Inner: Visit<T>> Visit<T> for Box<[Inner]> {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visit_iter(self.iter(), visitor)
    }
}

impl<T: Logic, Inner: Visit<T>> Visit<T> for &[Inner] {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visit_iter(self.iter(), visitor)
    }
}

impl<T: Logic, Inner: Visit<T>, const N: usize> Visit<T> for [Inner; N] {
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visit_iter(self.iter(), visitor)
    }
}

macro_rules! impl_visit_tuple {
    ($($x:ident),*) => {
        impl<T: Logic, $($x: Visit<T>),*> Visit<T> for ($($x),*) {
            fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
                #[allow(non_snake_case)]
                let &($(ref $x),*) = self;
                $(try_break!($x.visit_with(visitor));)*
                ControlFlow::CONTINUE
            }
        }
    };
}

impl_visit_tuple!(A, B);
impl_visit_tuple!(A, B, C);
impl_visit_tuple!(A, B, C, D);
impl_visit_tuple!(A, B, C, D, E);
