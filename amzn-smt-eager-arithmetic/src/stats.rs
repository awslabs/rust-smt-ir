//! Validation of quantifier-free ALL arithmetic SMT formulas.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::Constant;
use amzn_smt_ir::{
    logic::{
        all::{Op, ALL},
        ArithOp,
    },
    try_break,
    visit::{ControlFlow, SuperVisit, Visit, Visitor},
    CoreOp, Ctx, IConst, ICoreOp, IOp, ISort, ISymbol, IVar, QualIdentifier, Sorted, Term,
};
use anyhow::anyhow;
use ena::unify::{InPlaceUnificationTable, NoError, UnifyKey, UnifyValue};
use num_traits::Zero;
use smt2parser::Numeral;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt,
    hash::Hash,
    num::NonZeroU32,
    ops::Deref,
    rc::Rc,
};

#[derive(Clone)]
struct Stats {
    /// Integer constraints
    constraints: HashSet<Term>,
    /// Variables (to compute n = number of variables)
    vars: HashSet<ISymbol>,
    /// Upper bound on absolute value of coefficients
    mu_a: Numeral,
    /// Upper bound on absolute value of constants
    mu_b: Numeral,
    /// Upper bound on number of variables per non-separation constraint
    w: usize,
}

impl Default for Stats {
    fn default() -> Self {
        Self::new()
    }
}

enum SpecialCase {
    EqualityLogic,
    SeparationLogic,
    None { k: NonZeroU32 },
}

impl Stats {
    fn new() -> Self {
        Self {
            constraints: Default::default(),
            vars: HashSet::new(),
            mu_a: 1u8.into(),
            mu_b: 0u8.into(),
            w: 1,
        }
    }

    fn determine_special_case(&self) -> SpecialCase {
        use ArithOp::*;
        use Op::*;

        let (mut k, mut equality_logic) = (0, self.mu_b.is_zero());
        let bad = || {
            unreachable!(
                "only terms of the form `({<=,<,=,>=,>} (+ ...) ...)` are added to constraints"
            )
        };
        for t in self.constraints.iter() {
            if !matches!(t, Term::CoreOp(op) if matches!(op.as_ref(), CoreOp::Eq(..))) {
                equality_logic = false;
            }
            let args = match t {
                Term::CoreOp(op) => match op.as_ref() {
                    CoreOp::Eq(args) => args,
                    _ => bad(),
                },
                Term::OtherOp(op) => match op.as_ref() {
                    Arith(Gte(args) | Gt(args) | Lte(args) | Lt(args)) => args,
                    _ => bad(),
                },
                _ => bad(),
            };
            let lhs = match args.first() {
                Some(Term::OtherOp(op)) => match op.as_ref() {
                    Arith(Plus(args)) => args.as_slice(),
                    _ => bad(),
                },
                _ => bad(),
            };
            // Check if this is the LHS of a separation constraint (SC)
            match lhs {
                // x >= c (SC)
                [Term::Variable(_)] => {}
                // -x >= c === x <= -c (SC)
                [Term::OtherOp(op)]
                // x - y >= c (SC)
                | [Term::Variable(_), Term::OtherOp(op)]
                // y - x >= c (SC)
                | [Term::OtherOp(op), Term::Variable(_)]
                    if matches!(op.as_ref(), Arith(Neg(Term::Variable(_)))) => {}
                // Not a separation constraint
                _ => {
                    k += 1;
                }
            }
        }
        match NonZeroU32::new(k) {
            Some(k) => SpecialCase::None { k },
            None if equality_logic => SpecialCase::EqualityLogic,
            None => SpecialCase::SeparationLogic,
        }
    }

    /// See [`StatsVisitor::solution_size_upper_bound_bits()`].
    fn solution_size_upper_bound_bits(&self) -> u64 {
        use num_traits::One;
        use std::cmp::min;

        let (mu_a, mu_b) = (&self.mu_a, &self.mu_b);
        let (m, n) = (self.constraints.len(), self.vars.len());

        let bound = match self.determine_special_case() {
            SpecialCase::EqualityLogic => n.into(),
            SpecialCase::SeparationLogic => min(n, m) * (mu_b + Numeral::one()),
            SpecialCase::None { k } => {
                let s = min(n + 1, m);
                (mu_a * self.w).pow(k.get()) * (n + 2) * s * (mu_b + Numeral::one())
            }
        };

        // Need to search in [-d, d] where d is the bound
        // N-bit 2's complement represents the range [-2^(N-1), 2^(N-1)-1]
        // 2^(N-1)-1 >= d === 2^(N-1) >= d+1 === N-1 >= log2(d+1) === N >= log2(d+1)+1
        // To encode [-d, d] in 2's complement, need a width of ceil(log2(d+1)+1)
        (bound + Numeral::one()).bits() + 1
    }
}

impl fmt::Debug for Stats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let k = match self.determine_special_case() {
            SpecialCase::EqualityLogic | SpecialCase::SeparationLogic => 0,
            SpecialCase::None { k } => k.get(),
        };
        write!(
            f,
            "Stats {{ vars: {}, constraints: {}, a_max: {}, b_max: {}, k: {}, w: {} }}",
            self.vars.len(),
            self.constraints.len(),
            self.mu_a,
            self.mu_b,
            k,
            self.w
        )
    }
}

#[derive(Clone, Debug)]
struct StatsRef(Rc<RefCell<Stats>>);

impl Deref for StatsRef {
    type Target = RefCell<Stats>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<Stats> for StatsRef {
    fn from(stats: Stats) -> Self {
        Self(Rc::new(RefCell::new(stats)))
    }
}

impl UnifyValue for StatsRef {
    type Error = NoError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
        fn union<T: Clone + Hash + Eq>(mut s1: HashSet<T>, mut s2: HashSet<T>) -> HashSet<T> {
            if s2.len() > s1.len() {
                std::mem::swap(&mut s1, &mut s2)
            }
            s1.extend(s2);
            s1
        }
        let (value1, value2) = (value1.deref().take(), value2.deref().take());
        let stats = Stats {
            constraints: union(value1.constraints, value2.constraints),
            vars: union(value1.vars, value2.vars),
            mu_a: value1.mu_a.max(value2.mu_a),
            mu_b: value1.mu_b.max(value2.mu_b),
            w: value1.w.max(value2.w),
        };
        Ok(stats.into())
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct VarKey(u32);

impl UnifyKey for VarKey {
    type Value = StatsRef;
    fn index(&self) -> u32 {
        self.0
    }
    fn from_index(u: u32) -> Self {
        Self(u)
    }
    fn tag() -> &'static str {
        "VarKey"
    }
}

#[derive(Clone, Copy, Debug)]
enum Expecting {
    Formula,
    Sum,
    Summand,
    Coefficient,
    Variable,
    Rhs,
}

#[derive(Debug)]
pub struct StatsVisitor<'a> {
    expecting: Expecting,
    var_keys: HashMap<ISymbol, VarKey>,
    stats: InPlaceUnificationTable<VarKey>,
    current_partition: Option<VarKey>,
    context: &'a mut Ctx,
}

impl<'a> StatsVisitor<'a> {
    pub fn new(ctx: &'a mut Ctx) -> Self {
        Self {
            context: ctx,
            var_keys: Default::default(),
            stats: Default::default(),
            current_partition: None,
            expecting: Expecting::Formula,
        }
    }

    fn set_current_patition(&mut self, var: IVar<QualIdentifier>) {
        let stats = &mut self.stats;
        let key = *self
            .var_keys
            .entry(var.sym().clone())
            .or_insert_with(|| stats.new_key(Stats::new().into()));
        // If we're already in a partition, union the new partition with the old
        if let Some(old_key) = self.current_partition.take() {
            self.stats.union(key, old_key);
        }
        self.current_partition = Some(key);
    }

    fn current_partition_stats(&mut self) -> anyhow::Result<StatsRef> {
        let key = (self.current_partition.as_ref()).ok_or_else(|| anyhow!("Partition unset"))?;
        Ok(self.stats.probe_value(*key))
    }

    /// Determines an upper bound on the size of integer variables (number of bits/variable)
    /// for which a solution must exist if a formula is satisfiable. The formula must takes the
    /// form of linear constraints (for now just of the form `sum >= b` where `sum` is a linear
    /// combination of variables and `b` is a constant) joined by AND/OR/NOT. If the formula doesn't
    /// have the right form, the invalid subformula is returned as an error.
    /// See: <http://reports-archive.adm.cs.cmu.edu/anon/2003/CMU-CS-03-210.pdf>
    pub fn solution_size_upper_bound_bits(self) -> HashMap<ISymbol, u64> {
        let mut partition_bounds = HashMap::new();
        let mut stats = self.stats;
        let bounds = (self.var_keys.into_iter()).map(|(sym, key)| {
            let key = stats.find(key);
            let bound = *partition_bounds.entry(key).or_insert_with(|| {
                let stats = stats.probe_value(key);
                let stats = stats.borrow();
                let bound = stats.solution_size_upper_bound_bits();
                println!(
                    "Partition '{}': stats: {:?}, bound: {} bits",
                    sym, stats, bound
                );
                bound
            });
            (sym, bound)
        });
        bounds.collect()
    }

    fn invalid(&self, t: impl Into<Term>) -> anyhow::Error {
        Invalid(self.expecting, t.into()).into()
    }

    #[must_use]
    fn with_stats<T>(&mut self, f: impl FnOnce(&mut Stats) -> T) -> ControlFlow<anyhow::Error, T> {
        let stats = match self.current_partition_stats() {
            Ok(stats) => stats,
            Err(e) => return ControlFlow::Break(e),
        };
        let ret = f(&mut stats.borrow_mut());
        ControlFlow::Continue(ret)
    }

    fn visit_constraint(&mut self, t: Term, args: &[Term]) -> ControlFlow<anyhow::Error> {
        match args {
            [l, r] => {
                self.expecting = Expecting::Sum;
                try_break!(l.visit_with(self));
                debug_assert!(
                    self.current_partition.is_some(),
                    "constraints contain at least one variable: {}",
                    t
                );
                try_break!(self.with_stats(|stats| stats.constraints.insert(t)));
                self.expecting = Expecting::Rhs;
                try_break!(r.visit_with(self));
                self.expecting = Expecting::Formula;
                self.current_partition = None;
                ControlFlow::CONTINUE
            }
            _ => ControlFlow::Break(self.invalid(t)),
        }
    }
}

#[derive(Debug, thiserror::Error)]
#[error("Error computing statistics for Presburger formula: expected {0:?}, found {1}")]
pub struct Invalid(Expecting, Term);

impl Visitor<ALL> for StatsVisitor<'_> {
    type BreakTy = anyhow::Error;

    fn context(&self) -> Option<&Ctx> {
        Some(self.context)
    }
    fn context_mut(&mut self) -> Option<&mut Ctx> {
        Some(self.context)
    }

    fn visit_const(&mut self, c: &IConst) -> ControlFlow<Self::BreakTy> {
        match (self.expecting, c.as_ref()) {
            (Expecting::Coefficient, Constant::Numeral(a)) => self.with_stats(|stats| {
                if a > &stats.mu_a {
                    stats.mu_a = a.clone();
                }
            }),
            (Expecting::Rhs, Constant::Numeral(b)) => self.with_stats(|stats| {
                if b > &stats.mu_b {
                    stats.mu_b = b.clone();
                }
            }),
            _ => ControlFlow::Break(self.invalid(c.clone())),
        }
    }

    fn visit_var(&mut self, var: &IVar<QualIdentifier>) -> ControlFlow<Self::BreakTy> {
        match self.expecting {
            Expecting::Summand | Expecting::Variable | Expecting::Sum | Expecting::Rhs => {
                debug_assert_eq!(
                    self.context.const_sort(var.sym()),
                    Some(&ISort::int()),
                    "sums contain integer variables"
                );
                self.set_current_patition(var.clone());
                self.with_stats(|stats| {
                    stats.vars.insert(var.sym().clone());
                })
            }
            Expecting::Formula => {
                let sort = self.context.const_sort(var.sym());
                if sort == Some(&ISort::bool()) {
                    ControlFlow::CONTINUE
                } else {
                    ControlFlow::Break(self.invalid(var.clone()))
                }
            }
            _ => ControlFlow::Break(self.invalid(var.clone())),
        }
    }

    fn visit_core_op(&mut self, op: &ICoreOp<ALL>) -> ControlFlow<Self::BreakTy> {
        if !matches!(self.expecting, Expecting::Formula) {
            return ControlFlow::Break(self.invalid(op.clone()));
        }
        use CoreOp::*;
        match op.as_ref() {
            Distinct(..) | Ite(..) => ControlFlow::Break(self.invalid(op.clone())),
            Eq(args) if args.first().map(|t| t.sort(self.context)) != Some(Ok(ISort::bool())) => {
                self.visit_constraint(op.into(), args)
            }
            True | False | Not(..) | And(..) | Or(..) | Xor(..) | Imp(..) | Eq(..) => {
                op.super_visit_with(self)
            }
        }
    }

    fn visit_theory_op(&mut self, op: &IOp<ALL>) -> ControlFlow<Self::BreakTy> {
        use ArithOp::*;
        use Op::*;

        match (self.expecting, op.as_ref()) {
            (Expecting::Formula, Arith(Gte(args) | Gt(args) | Lte(args) | Lt(args))) => {
                self.visit_constraint(op.into(), args)
            }
            (Expecting::Formula, BitVec(..)) => ControlFlow::CONTINUE,
            (Expecting::Sum, Arith(Plus(args))) => {
                self.expecting = Expecting::Summand;
                try_break!(args.visit_with(self));
                debug_assert!(
                    self.current_partition.is_some(),
                    "+ contains at least one variable: {}",
                    op
                );
                self.with_stats(|stats| {
                    stats.w = stats.w.max(args.len());
                })
            }
            (Expecting::Rhs, Arith(Neg(b))) => b.visit_with(self),
            (Expecting::Coefficient, Arith(Neg(a))) => a.visit_with(self),
            (Expecting::Summand, Arith(Neg(x))) => {
                self.expecting = Expecting::Variable;
                try_break!(x.visit_with(self));
                self.expecting = Expecting::Summand;
                ControlFlow::CONTINUE
            }
            (exp @ (Expecting::Summand | Expecting::Rhs), Arith(Mul(args))) => {
                match args.as_slice() {
                    [a, x] => {
                        self.expecting = Expecting::Variable;
                        try_break!(x.visit_with(self));
                        self.expecting = Expecting::Coefficient;
                        try_break!(a.visit_with(self));
                        self.expecting = exp;
                        ControlFlow::CONTINUE
                    }
                    _ => ControlFlow::Break(self.invalid(op.clone())),
                }
            }
            _ => ControlFlow::Break(self.invalid(op.clone())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use amzn_smt_ir::Script;

    #[test]
    fn multiple_partitions() -> anyhow::Result<()> {
        let smt = "
            (declare-const x Int)
            (declare-const y Int)
            (assert (>= (+ x) 0))
            (assert (>= (+ y) 10))
        ";
        let script = Script::<Term>::parse(smt.as_bytes())?;
        let mut ctx = Ctx::default();
        let mut visitor = StatsVisitor::new(&mut ctx);
        assert!(matches!(
            script.visit_asserted(&mut visitor),
            ControlFlow::Continue(())
        ));
        let bounds = visitor.solution_size_upper_bound_bits();
        let bound = |x| bounds[&ISymbol::from(x)];
        assert_ne!(
            bound("x"),
            bound("y"),
            "x and y are in different variable classes with different bounds"
        );
        Ok(())
    }
}
