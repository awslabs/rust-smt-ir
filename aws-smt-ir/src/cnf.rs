// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    fold::{Fold, Folder},
    Command, CoreOp, IConst, ICoreOp, ILet, IMatch, IOp, IQuantifier, ISort, IVar, Logic, Script,
    Sorted, Term, IUF,
};
use itertools::Itertools;
use smallvec::{smallvec, SmallVec};
use std::{
    collections::{HashMap, HashSet},
    ffi::{OsStr, OsString},
    fmt::{self, Debug},
    io::{self, BufWriter, Write},
    iter,
    num::{NonZeroU64, ParseIntError},
    ops, process,
};

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Variable(NonZeroU64);

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<L: Logic> Sorted<L> for Variable {
    fn sort(&self, _: &mut crate::Ctx) -> Result<crate::ISort, crate::UnknownSort<Term<L>>> {
        Ok(ISort::bool())
    }
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum TransformationError<L: Logic> {
    #[error("CNF transformation doesn't support constants: {0}")]
    UnexpectedConst(IConst),
    #[error("CNF transformation doesn't support theory functions: {0}")]
    UnexpectedTheoryFunc(IOp<L>),
    #[error("CNF transformation doesn't support quantifiers: {0}")]
    UnexpectedQuantifier(IQuantifier<L>),
    #[error("CNF transformation doesn't support uninterpreted functions: {0}")]
    UnexpectedUF(IUF<L>),
    #[error("CNF transformation doesn't support `match`es: {0}")]
    UnexpectedMatch(IMatch<L>),
    #[error("CNF transformation doesn't support `let`s: {0}")]
    UnexpectedLet(ILet<L>),
}

macro_rules! clause {
    ($($x:expr),*) => {
        Clause(smallvec![$($x),*])
    };
}

type VarMap<V> = HashMap<IVar<V>, Variable>;

pub fn into_cnf<T: Logic>(
    script: Script<Term<T>>,
) -> Result<(CnfTerm, VarMap<T::Var>), TransformationError<T>> {
    let mut folder = CnfFolder::default();
    let mut cnf = CnfTerm::default();
    script
        .try_fold(&mut folder)?
        .into_iter()
        .for_each(|command| {
            if let Command::Assert { term: lit } = command {
                cnf.push(clause![lit])
            }
        });
    Ok((cnf.and(CnfTerm(folder.clauses)), folder.vars))
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct CnfTerm(Vec<Clause>);

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Clause(SmallVec<[Literal; 3]>);

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct Literal {
    var: Variable,
    sign: bool,
}

impl ops::Not for Literal {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self {
            var: self.var,
            sign: !self.sign,
        }
    }
}

impl Literal {
    fn new(var: Variable, sign: bool) -> Self {
        Self { var, sign }
    }

    fn t(var: Variable) -> Self {
        Self::new(var, true)
    }

    fn f(var: Variable) -> Self {
        Self::new(var, false)
    }
}

/// Converts a op into CNF (conjunctive normal form).
#[derive(Debug)]
struct CnfFolder<L: Logic> {
    next_var: NonZeroU64,
    vars: HashMap<IVar<L::Var>, Variable>,
    clauses: Vec<Clause>,
    cache: HashMap<ICoreOp<L>, Literal>,
}

impl<L: Logic> Default for CnfFolder<L> {
    fn default() -> Self {
        Self {
            next_var: NonZeroU64::new(1).unwrap(),
            vars: HashMap::new(),
            clauses: Default::default(),
            cache: Default::default(),
        }
    }
}

impl<L: Logic> CnfFolder<L>
where
    Self: Folder<L, Output = Literal, Error = TransformationError<L>>,
{
    fn inc(x: NonZeroU64) -> NonZeroU64 {
        let new = x.get().checked_add(1);
        new.and_then(NonZeroU64::new).unwrap()
    }

    fn var(&mut self, var: IVar<L::Var>) -> Variable {
        let next = &mut self.next_var;
        *(self.vars.entry(var)).or_insert_with(|| {
            let v = Variable(*next);
            *next = Self::inc(*next);
            v
        })
    }

    fn gen_var(&mut self) -> Variable {
        let v = Variable(self.next_var);
        self.next_var = Self::inc(self.next_var);
        v
    }

    fn assert(&mut self, t: Term<L>) -> Result<(), TransformationError<L>> {
        if let Term::CoreOp(op) = &t {
            match op.as_ref() {
                CoreOp::And(args) => return self.assert_and(args),
                CoreOp::Or(args) => return self.assert_or(args),
                _ => {}
            }
        }
        let lit = t.fold_with(self)?;
        self.clauses.push(clause![lit]);
        Ok(())
    }

    fn and(&mut self, args: &[Literal]) -> Literal {
        let out = Literal::t(self.gen_var());
        self.clauses.push(Clause(
            args.iter()
                .copied()
                .map(|lit| !lit)
                .chain(iter::once(out))
                .collect(),
        ));
        self.clauses
            .extend(args.iter().copied().map(|v| clause![v, !out]));
        out
    }

    fn assert_and(&mut self, args: &[Term<L>]) -> Result<(), TransformationError<L>> {
        for arg in args.iter().cloned() {
            self.assert(arg)?;
        }
        Ok(())
    }

    fn nand(&mut self, args: &[Literal]) -> Literal {
        let out = Literal::t(self.gen_var());
        self.clauses.push(Clause(
            args.iter()
                .copied()
                .chain(iter::once(out))
                .map(|t| !t)
                .collect(),
        ));
        self.clauses
            .extend(args.iter().copied().map(|v| clause![v, out]));
        out
    }

    fn or(&mut self, args: &[Literal]) -> Literal {
        let out = Literal::t(self.gen_var());
        self.clauses.push(Clause(
            (args.iter().copied()).chain(iter::once(!out)).collect(),
        ));
        self.clauses.extend(args.iter().map(|&v| clause![!v, out]));
        out
    }

    fn assert_or(&mut self, args: &[Term<L>]) -> Result<(), TransformationError<L>> {
        let literal_args = args.iter().map(|t| match t {
            Term::Variable(v) => Some(Literal::t(self.var(v.clone()))),
            Term::CoreOp(op) => match op.as_ref() {
                CoreOp::Not(Term::Variable(v)) => Some(Literal::f(self.var(v.clone()))),
                _ => None,
            },
            _ => None,
        });
        if let Some(args) = literal_args.collect() {
            self.clauses.push(Clause(args));
        } else {
            let args = args.fold_with(self)?;
            let clause = clause![self.or(&args)];
            self.clauses.push(clause);
        }
        Ok(())
    }

    fn nor(&mut self, args: &[Literal]) -> Literal {
        let out = Literal::t(self.gen_var());
        self.clauses.push(Clause(
            args.iter().copied().chain(iter::once(out)).collect(),
        ));
        self.clauses
            .extend(args.iter().copied().map(|v| clause![!v, !out]));
        out
    }

    fn xor(&mut self, args: impl IntoIterator<Item = Literal>) -> Literal {
        let xor = |a: Literal, b: Literal| {
            let out = Literal::t(self.gen_var());
            self.clauses.extend([
                clause![!a, !b, !out],
                clause![a, b, !out],
                clause![a, !b, out],
                clause![!a, b, out],
            ]);
            out
        };
        // TODO: is there a better encoding for variadic XOR?
        args.into_iter()
            .reduce(xor)
            .unwrap_or_else(|| self.fold_core_op(false.into()).unwrap())
    }

    fn xnor(&mut self, args: impl IntoIterator<Item = Literal>) -> Literal {
        let xnor = |a: Literal, b: Literal| {
            let out = Literal::t(self.gen_var());
            self.clauses.extend([
                clause![!a, !b, out],
                clause![a, b, out],
                clause![a, !b, !out],
                clause![!a, b, !out],
            ]);
            out
        };
        let mut args = args.into_iter().peekable();
        match (args.next(), args.peek()) {
            (None, None) => self.fold_core_op(true.into()).unwrap(),
            (Some(first), None) => !first,
            (Some(first), Some(_)) => args.fold(first, xnor),
            (None, Some(_)) => unreachable!("iterators always yield None after the first None"),
        }
    }

    fn imp<Iter>(&mut self, args: Iter) -> Literal
    where
        Iter: IntoIterator<Item = Literal>,
        Iter::IntoIter: DoubleEndedIterator,
    {
        let mut imp = |a: Literal, b| {
            let out = Literal::t(self.gen_var());
            self.clauses
                .extend([clause![!a, b, !out], clause![a, out], clause![!b, out]]);
            out
        };
        args.into_iter().rev().reduce(|b, a| imp(a, b)).unwrap()
    }

    fn eq(&mut self, args: impl IntoIterator<Item = Literal>) -> Literal {
        let mut eq = |a, b: Literal| {
            let out = Literal::t(self.gen_var());
            self.clauses.extend([
                clause![a, !b, !out],
                clause![!a, b, !out],
                clause![!a, !b, out],
                clause![a, b, out],
            ]);
            out
        };
        let constraints: Vec<_> = args
            .into_iter()
            .tuple_windows()
            .map(|(a, b)| eq(a, b))
            .collect();
        self.and(&constraints)
    }
}

impl<T: Logic> Folder<T> for CnfFolder<T> {
    type Output = Literal;
    type Error = TransformationError<T>;

    fn fold_assert(&mut self, asserted: Term<T>) -> Result<Command<Self::Output>, Self::Error> {
        // `assert()` adds clauses directly to `self.clauses` and the resulting terms are visible
        // only inside this module, so we replace each assert with a dummy command
        let dummy = Command::CheckSat;
        self.assert(asserted).map(|()| dummy)
    }

    fn fold_const(&mut self, constant: IConst) -> Result<Self::Output, Self::Error> {
        Err(TransformationError::UnexpectedConst(constant))
    }

    fn fold_var(&mut self, var: IVar<T::Var>) -> Result<Self::Output, Self::Error> {
        Ok(Literal::t(self.var(var)))
    }

    fn fold_core_op(&mut self, op: ICoreOp<T>) -> Result<Self::Output, Self::Error> {
        if let Some(out) = self.cache.get(&op) {
            return Ok(*out);
        }

        use CoreOp::*;

        let encoded = match op.as_ref() {
            True => {
                let v = Literal::t(self.gen_var());
                self.clauses.push(clause![v]);
                v
            }
            False => {
                let v = Literal::t(self.gen_var());
                self.clauses.push(clause![!v]);
                v
            }
            Not(arg) => {
                let mut standard = || -> Result<_, Self::Error> {
                    let arg = arg.fold_with(self)?;
                    Ok(!arg)
                };
                if let Term::CoreOp(op) = arg {
                    match op.as_ref() {
                        CoreOp::Not(t) => t.fold_with(self)?,
                        CoreOp::And(args) => {
                            let args = args.fold_with(self)?;
                            self.nand(&args)
                        }
                        CoreOp::Or(args) => {
                            let args = args.fold_with(self)?;
                            self.nor(&args)
                        }
                        CoreOp::Xor(args) => {
                            let args = args.fold_with(self)?;
                            self.xnor(args)
                        }
                        _ => standard()?,
                    }
                } else {
                    standard()?
                }
            }
            And(args) => {
                let args = args.fold_with(self)?;
                self.and(&args)
            }
            Or(args) => {
                let args = args.fold_with(self)?;
                self.or(&args)
            }
            Xor(args) => {
                let args = args.fold_with(self)?;
                self.xor(args)
            }
            Imp(args) => {
                let args = args.fold_with(self)?;
                self.imp(args)
            }
            Eq(args) => {
                let args = args.fold_with(self)?;
                self.eq(args)
            }
            Distinct(args) => {
                let args = args.fold_with(self)?;
                let constraints: Vec<_> = args
                    .into_iter()
                    .tuple_combinations()
                    .map(|(a, b)| self.xor([a, b]))
                    .collect();
                self.and(&constraints)
            }
            Ite(i, consq, alt) => {
                let (i, consq, alt) = (
                    i.fold_with(self)?,
                    consq.fold_with(self)?,
                    alt.fold_with(self)?,
                );
                let true_constraint = self.imp([i, consq]);
                let false_constraint = self.imp([!i, alt]);
                self.and(&[true_constraint, false_constraint])
            }
        };

        self.cache.insert(op, encoded);
        Ok(encoded)
    }

    fn fold_theory_op(&mut self, op: IOp<T>) -> Result<Self::Output, Self::Error> {
        Err(TransformationError::UnexpectedTheoryFunc(op))
    }

    fn fold_let(&mut self, l: ILet<T>) -> Result<Self::Output, Self::Error> {
        // TODO: support this once `Logic::Var` no longer exists.
        Err(TransformationError::UnexpectedLet(l))
    }

    fn fold_match(&mut self, m: IMatch<T>) -> Result<Self::Output, Self::Error> {
        Err(TransformationError::UnexpectedMatch(m))
    }

    fn fold_quantifier(&mut self, quantifier: IQuantifier<T>) -> Result<Self::Output, Self::Error> {
        Err(TransformationError::UnexpectedQuantifier(quantifier))
    }

    fn fold_uninterpreted_func(&mut self, func: IUF<T>) -> Result<Self::Output, Self::Error> {
        Err(TransformationError::UnexpectedUF(func))
    }
}

#[derive(Debug, thiserror::Error)]
pub enum SolveError {
    #[error("Unable to run solver {0:?}")]
    RunSolver(OsString, #[source] io::Error),
    #[error("Unable to write CNF to solver stdin")]
    WriteProblem(#[source] io::Error),
    #[error("Unable to read solver output")]
    ReadOutput(#[source] io::Error),
    #[error("No solution line 's <SAT|UNSAT>'")]
    NoSolutionLine,
    #[error("Malformed solution line: {0}")]
    BadSolutionLine(String),
    #[error("Malformed variable assignment '{0}'")]
    MalformedAssignment(String, #[source] ParseIntError),
}

impl CnfTerm {
    #[cfg(test)]
    fn singleton(lit: Literal) -> CnfTerm {
        CnfTerm(vec![Clause(smallvec![lit])])
    }

    fn push(&mut self, clause: Clause) {
        self.0.push(clause);
    }

    fn and(mut self, mut other: Self) -> Self {
        if other.0.len() > self.0.len() {
            std::mem::swap(&mut self.0, &mut other.0);
        }
        self.0.extend(other.0);
        self
    }

    /// Solves a CNF formula using a SAT solver and returns an assignment of true/false to variables
    /// that makes the formula true, if such an assignment exists.
    pub fn solve_with(
        self,
        solver: impl AsRef<OsStr>,
    ) -> Result<Option<HashMap<Variable, bool>>, SolveError> {
        let solver = solver.as_ref();
        let mut process = process::Command::new(solver)
            .stdin(process::Stdio::piped())
            .stdout(process::Stdio::piped())
            .spawn()
            .map_err(|err| SolveError::RunSolver(solver.to_owned(), err))?;
        self.write_dimacs(process.stdin.as_mut().unwrap())
            .map_err(SolveError::WriteProblem)?;
        drop(self); // Free up some memory
        let output = process
            .wait_with_output()
            .map_err(|err| SolveError::RunSolver(solver.to_owned(), err))?;
        Self::parse_dimacs_solution(output.stdout.as_slice())
    }

    /// Solves a CNF formula using varisat, a Rust SAT solver library. This does not require having
    /// a separate SAT solver installed.
    #[cfg(any(test, feature = "varisat"))]
    pub fn solve_with_varisat(self) -> Result<Option<HashMap<Variable, bool>>, SolveError> {
        use varisat::solver::Solver;
        let mut solver = Solver::new();
        let mut dimacs = Vec::new();
        self.write_dimacs(io::Cursor::new(&mut dimacs))
            .map_err(SolveError::WriteProblem)?;
        drop(self); // Free up some memory
        solver
            .add_dimacs_cnf(dimacs.as_slice())
            .expect("Reading from a Vec can't fail");
        drop(dimacs); // Free up some memory
        let model = solver.solve().unwrap().then(|| solver.model().unwrap());
        match model {
            Some(model) => {
                let assignments = model.into_iter().map(|lit| {
                    let var = Variable(NonZeroU64::new(lit.index() as u64 + 1).unwrap());
                    (var, lit.is_positive())
                });
                Ok(Some(assignments.collect()))
            }
            None => Ok(None),
        }
    }

    /// Produces the number of clauses in the formula.
    pub fn num_clauses(&self) -> usize {
        self.0.len()
    }

    pub fn num_vars(&self) -> u64 {
        (self.0.iter())
            .flat_map(|clause| &clause.0)
            .map(|lit| lit.var.0)
            .max()
            .map(NonZeroU64::get)
            .unwrap_or(0)
    }

    /// Determines the number of clauses that appear multiple times in the formula.
    pub fn num_duplicate_clauses(&self) -> usize {
        self.num_clauses() - self.0.iter().collect::<HashSet<_>>().len()
    }

    /// Writes a CNF SAT formula to a sink in the DIMACS format.
    pub fn write_dimacs(&self, f: impl Write) -> io::Result<()> {
        let mut f = BufWriter::new(f);
        writeln!(f, "p cnf {} {}", self.num_vars(), self.num_clauses())?;
        for clause in &self.0 {
            for literal in &clause.0 {
                write!(f, "{} ", literal)?;
            }
            writeln!(f, "0")?;
        }
        Ok(())
    }

    /// Parses a DIMACS solution from a reader, returning a mapping from variables to signs
    /// if a satisfying assignment exists or `None` if not.
    pub fn parse_dimacs_solution(
        output: impl io::BufRead,
    ) -> Result<Option<HashMap<Variable, bool>>, SolveError> {
        let mut lines = output
            .lines()
            .map(|res| res.map_err(SolveError::ReadOutput));

        loop {
            let l = lines.next().ok_or(SolveError::NoSolutionLine)??;
            match l.strip_prefix("s ") {
                Some("UNSATISFIABLE") => return Ok(None),
                Some("SATISFIABLE") => break,
                Some(_) => return Err(SolveError::BadSolutionLine(l)),
                None => continue,
            }
        }

        let mut model = HashMap::new();

        while let Some(l) = lines.next().transpose()? {
            if let Some(l) = l.strip_prefix("v ") {
                for assignment in l.split(' ').filter(|&x| x != "0") {
                    let (var, sign) = if let Some(var) = assignment.strip_prefix('-') {
                        (var, false)
                    } else {
                        (assignment, true)
                    };
                    let var = var
                        .parse()
                        .map_err(|err| SolveError::MalformedAssignment(var.to_string(), err))?;
                    model.insert(Variable(var), sign);
                }
            }
        }

        Ok(Some(model))
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sign = if self.sign { "" } else { "-" };
        write!(f, "{}{}", sign, self.var.0)
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        let mut lits = self.0.iter();
        if let Some(lit) = lits.next() {
            write!(f, "{}", lit)?;
            for lit in lits {
                write!(f, " ∨ {}", lit)?;
            }
        }
        write!(f, ")")
    }
}

impl fmt::Display for CnfTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        let mut clauses = self.0.iter();
        if let Some(clause) = clauses.next() {
            write!(f, "{}", clause)?;
            for clause in clauses {
                write!(f, " ∧ {}", clause)?;
            }
        }
        write!(f, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aws_smt_ir::{args, fold::Fold, Logic, Void};
    use paste::paste;
    use std::iter::FromIterator;

    #[derive(Clone, Copy, Default, Debug, Hash, PartialEq, Eq)]
    struct L;
    impl Logic for L {
        type Var = Variable;
        type Op = Void;
        type Quantifier = Void;
        type UninterpretedFunc = Void;
    }

    macro_rules! check {
        (|$($input:ident),*| $body:expr, [$([$($in:expr),* => $out:expr]),*$(,)?]) => {
            {
                $(let $input = true;)*
                match [$($input),*] {
                    $([$($in),*] => (),)*
                }
            }
            for [$(paste!([<$input _val>])),*, out] in [$([$($in),*, $out]),*] {
                let mut gen_var = {
                    let mut x = 0;
                    move || {
                        x += 1;
                        var(x)
                    }
                };
                $(let $input = gen_var();)*
                let mut folder = CnfFolder::default();
                let make = |$($input),*| $body;
                let v = Term::<L>::from(make(
                    $(IVar::from($input).into()),*
                ))
                .fold_with(&mut folder)
                .unwrap();
                let cnf = CnfTerm(folder.clauses);

                let cnf = cnf$(.and(CnfTerm::singleton(Literal::new($input, paste!([<$input _val>])))))*;
                let expected_output = if out {
                    v
                } else {
                    !v
                };
                assert!(
                    cnf.clone().and(CnfTerm::singleton(expected_output)).solve_with_varisat().unwrap().is_some(),
                    "{}: {:?} => {} is SAT",
                    stringify!($body), [$(paste!([<$input _val>])),*], out
                );
                assert!(
                    cnf.and(CnfTerm::singleton(!expected_output)).solve_with_varisat().unwrap().is_none(),
                    "{}: {:?} => {} is UNSAT",
                    stringify!($body), [$(paste!([<$input _val>])),*], !out
                );
            }
        };
    }

    #[test]
    fn op_encoding() {
        check!(
            |a, b| CoreOp::And([a, b].into()),
            [
                [true, true => true],
                [true, false => false],
                [false, true => false],
                [false, false => false],
            ]
        );
        check!(|a| CoreOp::And(args![a]), [[true => true], [false => false]]);
        check!(
            |a, b| !Term::from(CoreOp::And([a, b].into())),
            [
                [true, true => false],
                [true, false => true],
                [false, true => true],
                [false, false => true],
            ]
        );
        check!(|a| !Term::from(CoreOp::And(args![a])), [[true => false], [false => true]]);
        check!(
            |a, b| CoreOp::Or([a, b].into()),
            [
                [true, true => true],
                [true, false => true],
                [false, true => true],
                [false, false => false],
            ]
        );
        check!(|a| CoreOp::Or(args![a]), [[true => true], [false => false]]);
        check!(
            |a, b| !Term::from(CoreOp::Or([a, b].into())),
            [
                [true, true => false],
                [true, false => false],
                [false, true => false],
                [false, false => true],
            ]
        );
        check!(|a| !Term::from(CoreOp::Or(args![a])), [[true => false], [false => true]]);
        check!(
            |a, b| CoreOp::Xor([a, b].into()),
            [
                [true, true => false],
                [true, false => true],
                [false, true => true],
                [false, false => false],
            ]
        );
        check!(|a| CoreOp::Xor(args![a]), [[true => true], [false => false]]);
        check!(
            |a, b| !Term::from(CoreOp::Xor([a, b].into())),
            [
                [true, true => true],
                [true, false => false],
                [false, true => false],
                [false, false => true],
            ]
        );
        check!(|a| !Term::from(CoreOp::Xor(args![a])), [[true => false], [false => true]]);
        check!(
            |a, b| CoreOp::Imp([a, b].into()),
            [
                [true, true => true],
                [true, false => false],
                [false, true => true],
                [false, false => true],
            ]
        );
        check!(
            |a, b| CoreOp::Eq([a, b].into()),
            [
                [true, true => true],
                [true, false => false],
                [false, true => false],
                [false, false => true],
            ]
        );
        check!(|a| CoreOp::Eq(args![a]), [[true => true], [false => true]]);
        check!(
            |a, b| CoreOp::Distinct([a, b].into()),
            [
                [true, true => false],
                [true, false => true],
                [false, true => true],
                [false, false => false],
            ]
        );
        check!(|a| CoreOp::Distinct(args![a]), [[true => true], [false => true]]);
        check!(
            |i, t, e| CoreOp::Ite(i, t, e),
            [
                [true, true, true => true],
                [true, true, false => true],
                [true, false, true => false],
                [true, false, false => false],
                [false, true, true => true],
                [false, true, false => false],
                [false, false, true => true],
                [false, false, false => false],
            ]
        );
    }

    #[test]
    fn trivially_unsat() {
        let formula = CnfTerm(vec![Clause(smallvec![])]);
        assert!(matches!(formula.solve_with_varisat(), Ok(None)));
    }

    #[test]
    fn trivially_sat() {
        let formula = CnfTerm(vec![]);
        assert_eq!(
            formula.solve_with_varisat().unwrap().unwrap(),
            HashMap::new()
        );
    }

    fn var(x: u64) -> Variable {
        Variable(NonZeroU64::new(x).unwrap())
    }

    #[test]
    fn sat() {
        let (x, y) = (var(1), var(2));
        let formula = CnfTerm(vec![Clause(smallvec![Literal { var: x, sign: true }])]);
        assert_eq!(
            formula.solve_with_varisat().unwrap().unwrap(),
            HashMap::from_iter(vec![(x, true)])
        );
        let formula = CnfTerm(vec![
            Clause(smallvec![Literal { var: x, sign: true }]),
            Clause(smallvec![Literal {
                var: y,
                sign: false
            }]),
        ]);
        assert_eq!(
            formula.solve_with_varisat().unwrap().unwrap(),
            HashMap::from_iter(vec![(x, true), (y, false)])
        );
    }
}
