// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    fold::{Fold, IntraLogicFolder},
    Ctx, ISymbol, IVar, Logic, QualIdentifier, Term,
};
use std::convert::Infallible;

struct Substituter<'a, L: Logic> {
    ctx: Ctx,
    replacements: &'a [(ISymbol, Term<L>)],
}

impl<'a, L: Logic> Substituter<'a, L> {
    fn new(replacements: &'a [(ISymbol, Term<L>)]) -> Self {
        Self {
            ctx: Default::default(),
            replacements,
        }
    }
}

impl<L: Logic<Var = QualIdentifier>> IntraLogicFolder<L> for Substituter<'_, L> {
    type Error = Infallible;

    fn context(&self) -> Option<&Ctx> {
        Some(&self.ctx)
    }

    fn context_mut(&mut self) -> Option<&mut Ctx> {
        Some(&mut self.ctx)
    }

    fn fold_var(&mut self, var: IVar<L::Var>) -> Result<Term<L>, Self::Error> {
        if self.ctx.local.is_free(var.sym()) {
            if let Some((_, t)) = self
                .replacements
                .iter()
                .rev()
                .find(|(sym, _)| sym == var.sym())
            {
                return Ok(t.clone());
            }
        }
        Ok(Term::from(var))
    }
}

impl<L: Logic<Var = QualIdentifier>> Term<L> {
    /// Substitutes terms in for variables according to the pairs in `replacements`.
    pub fn substitute(self, replacements: &[(ISymbol, Self)]) -> Self {
        match self.fold_with(&mut Substituter::new(replacements)) {
            Ok(t) => t,
            Err(e) => match e {},
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inner_bindings() {
        let t: Term = "(let ((x true)) (and x y))".parse().unwrap();
        assert_eq!(
            t.clone().substitute(&[("y".into(), true.into())]),
            "(let ((x true)) (and x true))".parse().unwrap()
        );
        // x is bound by a new let, so it shouldn't be substituted
        assert_eq!(t.clone().substitute(&[("x".into(), true.into())]), t);
    }
}
