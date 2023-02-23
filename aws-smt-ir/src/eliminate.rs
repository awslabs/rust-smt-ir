use crate::{
    fold::{Fold, IntraLogicFolder},
    CoreOp, Ctx, FreshVarError, ILet, ISymbol, IVar, Logic, QualIdentifier, Script, Sorted, Term,
    UnknownSort,
};
use std::collections::HashMap;

#[derive(Debug)]
struct EliminateLets<'a, L: Logic> {
    ctx: &'a mut Ctx,
    substitutions: HashMap<ISymbol, Term<L>>,
    asserts: Vec<Term<L>>,
}

/// Eliminates `let` binders inside a script's terms through substitution.
/// To avoid exponential formula blowup, variables bound to non-constant-sized terms (e.g. function
/// applications, quantifiers, other let bindings) are replaced with appropriately constrained
/// constant declarations. For instance, `(assert (let ((x (+ 1 2))) (= x 3)))` could produce
/// ```text
/// (declare-const x Int)
/// (assert (= x (+ 1 2)))
/// (assert (= x 3))
/// ```
pub fn eliminate_lets<L: Logic<Var = QualIdentifier>>(
    ctx: &mut Ctx,
    script: Script<Term<L>>,
) -> Result<Script<Term<L>>, EliminationError<L>> {
    let mut folder = EliminateLets::new(ctx);
    let mut script = script.try_fold(&mut folder)?;
    script.add_asserts(folder.asserts.into_iter());
    Ok(script)
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum EliminationError<L: Logic> {
    #[error(transparent)]
    FreshVar(#[from] FreshVarError),
    #[error(transparent)]
    UnknownSort(#[from] UnknownSort<Term<L>>),
}

impl<'a, L: Logic> EliminateLets<'a, L> {
    pub fn new(ctx: &'a mut Ctx) -> Self {
        Self {
            ctx,
            substitutions: Default::default(),
            asserts: Default::default(),
        }
    }
}

impl<L: Logic<Var = QualIdentifier>> IntraLogicFolder<L> for EliminateLets<'_, L> {
    type Error = EliminationError<L>;

    fn context(&self) -> Option<&Ctx> {
        Some(self.ctx)
    }

    fn context_mut(&mut self) -> Option<&mut Ctx> {
        Some(self.ctx)
    }

    fn fold_var(&mut self, var: IVar) -> Result<Term<L>, Self::Error> {
        Ok(if let Some(t) = self.substitutions.get(var.sym()) {
            t.clone()
        } else {
            var.into()
        })
    }

    fn fold_let(&mut self, l: ILet<L>) -> Result<Term<L>, Self::Error> {
        let bindings: Vec<_> = (l.bindings.iter())
            .map(|(sym, t)| {
                // Eliminate lets and let-bound variables inside bindings
                let t = t.clone().fold_with(self)?;
                // If term adds any layers of nesting (i.e. isn't just a constant, variable, etc.),
                // introduce a new variable to represent it to avoid formula blowup
                let t = match &t {
                    Term::Constant(..) | Term::Variable(..) => t,
                    Term::CoreOp(op) if matches!(op.as_ref(), CoreOp::True | CoreOp::False) => t,
                    _ => {
                        let sort = t.sort(self.ctx)?;
                        let v = Term::from(self.ctx.fresh_var(sort)?);
                        self.asserts.push(CoreOp::Eq([v.clone(), t].into()).into());
                        v
                    }
                };
                Ok((sym, t))
            })
            .collect::<Result<_, Self::Error>>()?;
        let old: Vec<_> = (bindings.into_iter())
            .map(|(sym, t)| {
                let old = self.substitutions.insert(sym.clone(), t);
                (sym, old)
            })
            .collect();
        let out = l.term.clone().fold_with(self)?;
        for (sym, old) in old {
            debug_assert!(self.substitutions.contains_key(sym));
            if let Some(old) = old {
                self.substitutions.insert(sym.clone(), old);
            } else {
                self.substitutions.remove(sym);
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_terms_eq_after_elimination(before: &str, after: &str) {
        assert_eq!(
            eliminate_lets(
                &mut Ctx::default(),
                format!("(assert {})", before)
                    .parse::<Script<Term>>()
                    .unwrap()
            )
            .unwrap(),
            format!("(assert {})", after).parse().unwrap()
        );
    }

    #[test]
    fn basic() {
        assert_terms_eq_after_elimination("(let ((x 5)) (let ((y 4)) (+ x y)))", "(+ 5 4)");
    }

    #[test]
    fn substitutes_inside_bound_terms() {
        assert_terms_eq_after_elimination("(let ((x 5)) (let ((y x)) (+ x y)))", "(+ 5 5)");
    }

    #[test]
    fn simultaneous_bindings() {
        assert_terms_eq_after_elimination(
            "(let ((x false)) (let ((x true) (y x)) (and x y)))",
            "(and true false)",
        );
    }
}
