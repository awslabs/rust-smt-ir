// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    convert::{Converter, InvalidTerm},
    fold::{Fold, Folder},
    try_break,
    visit::{ControlFlow, Visit, Visitor},
    Command, ISort, ISymbol, IVar, Logic, QualIdentifier, Term,
};
use smt2parser::{CommandStream, Numeral};
use std::{
    collections::HashMap,
    convert::Infallible,
    fmt::{self, Debug, Display},
    io,
    iter::FromIterator,
    str::FromStr,
    sync::atomic,
};

/// `Script` represents an entire SMT-LIB script i.e. sequence of commands.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Script<Term> {
    commands: Vec<Command<Term>>,
}

impl<Term: Display> Display for Script<Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for command in self.commands.iter() {
            writeln!(f, "{}", command)?;
        }
        Ok(())
    }
}

impl<Term> FromIterator<Command<Term>> for Script<Term> {
    fn from_iter<T: IntoIterator<Item = Command<Term>>>(iter: T) -> Self {
        let commands = iter.into_iter().collect();
        Self { commands }
    }
}

impl<Term> IntoIterator for Script<Term> {
    type Item = Command<Term>;
    type IntoIter = std::vec::IntoIter<Command<Term>>;
    fn into_iter(self) -> Self::IntoIter {
        self.commands.into_iter()
    }
}

impl<Term> Extend<Command<Term>> for Script<Term> {
    fn extend<T: IntoIterator<Item = Command<Term>>>(&mut self, iter: T) {
        self.commands.extend(iter)
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ParseError<L: Logic> {
    #[error("malformed SMT-LIB input: {0}")]
    Smt2Parser(#[from] smt2parser::Error),
    #[error("invalid SMT-LIB expression in logic {0:?}: {1}")]
    Conversion(L, InvalidTerm<L>),
}

impl<L: Logic, T: Into<InvalidTerm<L>>> From<T> for ParseError<L> {
    fn from(t: T) -> Self {
        Self::Conversion(L::default(), t.into())
    }
}

impl<T: Logic> FromStr for Script<Term<T>>
where
    QualIdentifier: Into<T::Var>,
{
    type Err = ParseError<T>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s.as_bytes())
    }
}

impl<T: Logic> Script<Term<T>>
where
    QualIdentifier: Into<T::Var>,
{
    /// Parses a script from an SMT-LIB reader.
    ///
    /// # Examples
    ///
    /// ## Parsing a script from a string
    ///
    /// This example parses a simple SMT-LIB script into [`Terms`] in [`ALL`](crate::logic::ALL)
    /// (the most general logic).
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use amzn_smt_ir::{Script, logic::ALL, Term};
    /// let smt = "
    ///     (declare-const x Int)
    ///     (assert (= x 3))
    ///     (check-sat)
    /// ".as_bytes();
    /// let script = Script::<Term>::parse(smt)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn parse(smt: impl io::BufRead) -> Result<Self, ParseError<T>> {
        CommandStream::new(smt, Converter::<T>::default(), None).collect()
    }
}

impl<T: Logic> Script<Term<T>> {
    /// Visits each asserted term in the script with a [`Visitor`].
    #[must_use]
    pub fn visit_asserted<V: Visitor<T>>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        for command in self.commands.iter() {
            match command {
                Command::Assert(t) => try_break!(t.visit_with(visitor)),
                cmd => {
                    if let Some(ctx) = visitor.context_mut() {
                        ctx.process(cmd)
                    }
                }
            }
        }
        ControlFlow::CONTINUE
    }

    /// Folds each command in the script with a [`Folder`] that has [`Infallible`] as its `Error` type.
    pub fn fold<F: Folder<T, M, Error = Infallible>, M>(self, folder: &mut F) -> Script<F::Output> {
        let commands = (self.commands.into_iter())
            .map(|command| match command.fold_with(folder) {
                Ok(cmd) => cmd,
                Err(e) => match e {},
            })
            .collect();
        Script { commands }
    }

    /// Folds each command in the script with a [`Folder`].
    pub fn try_fold<F: Folder<T, M>, M>(
        self,
        folder: &mut F,
    ) -> Result<Script<F::Output>, F::Error> {
        let commands = (self.commands.into_iter())
            .map(|command| command.fold_with(folder))
            .collect::<Result<_, _>>()?;
        Ok(Script { commands })
    }
}

impl<Term> Script<Term> {
    /// Produces an iterator over the asserted terms in the script.
    pub fn into_asserted_terms(self) -> impl Iterator<Item = Term> {
        self.commands
            .into_iter()
            .filter_map(|command| match command {
                Command::Assert(t) => Some(t),
                _ => None,
            })
    }

    /// Maps a fallible function over the commands in a script.
    pub fn try_map<U, E>(
        self,
        f: impl FnMut(Command<Term>) -> Result<Command<U>, E>,
    ) -> Result<Script<U>, E> {
        let commands = (self.commands.into_iter())
            .map(f)
            .collect::<Result<_, _>>()?;
        Ok(Script { commands })
    }

    /// Maps a function over the commands in a script.
    pub fn map<U>(self, mut f: impl FnMut(Command<Term>) -> Command<U>) -> Script<U> {
        self.try_map(|cmd| Ok::<_, Infallible>(f(cmd))).unwrap()
    }

    /// Appends a sequence of asserted terms to a script before the final `(check-sat)` command.
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use amzn_smt_ir::{Script, Term, logic::ALL};
    /// let smt = "(assert true) (check-sat)".as_bytes();
    /// let mut script: Script<Term> = Script::parse(smt)?;
    /// script.add_asserts([Term::from(false)]);
    /// let expected = Script::parse("(assert true) (assert false) (check-sat)".as_bytes())?;
    /// assert_eq!(script, expected);
    /// # Ok(())
    /// # }
    /// ```
    pub fn add_asserts(&mut self, asserts: impl IntoIterator<Item = Term>) {
        let asserts = asserts.into_iter().map(Command::Assert);
        let check_sat_idx = (self.commands.iter())
            .enumerate()
            .rev()
            .find(|(_, cmd)| matches!(cmd, Command::CheckSat | Command::CheckSatAssuming { .. }));
        if let Some((idx, _)) = check_sat_idx {
            // Insert elements before the `(check-sat)`
            let after: Vec<_> = self.commands.drain(idx..).collect();
            self.extend(asserts);
            self.extend(after);
        } else {
            self.extend(asserts);
        }
    }
}

/// `Ctx` tracks the global context of a script (e.g. defined sorts and functions), along with local
/// context inside of terms (e.g. variables bound by `let`, `forall`, `exists`).
#[derive(Clone, Debug, Default)]
pub struct Ctx {
    pub(crate) script: ScriptCtx,
    pub(crate) local: LocalCtx,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LocalCtx {
    bound_vars: HashMap<ISymbol, Option<ISort>>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ScriptCtx {
    sorts: HashMap<ISymbol, SortSignature>,
    funs: HashMap<ISymbol, FunctionSignature>,
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
#[error("fresh variable counter overflowed u64::MAX")]
pub struct FreshVarError;

impl Ctx {
    /// Generates a variable that is not present in any expression processed by the solver using
    /// the `@` prefix reserved for solver-generated variables and a global variable counter to
    /// ensure uniqueness. However, this can only generate a finite number of variables (currently
    /// [`u64::MAX`]) before the counter overflows -- after that, `None` will be returned.
    pub fn fresh_var(&mut self, sort: ISort) -> Result<IVar<QualIdentifier>, FreshVarError> {
        Self::fresh_var_untracked().map(|var| {
            self.declare_const(var.sym().clone(), sort);
            var
        })
    }

    pub(crate) fn fresh_var_untracked() -> Result<IVar<QualIdentifier>, FreshVarError> {
        static NEXT: atomic::AtomicU64 = atomic::AtomicU64::new(0);
        static OVERFLOWED: atomic::AtomicBool = atomic::AtomicBool::new(false);
        let x = NEXT.fetch_add(1, atomic::Ordering::Relaxed);
        if x == u64::MAX {
            OVERFLOWED.store(true, atomic::Ordering::Relaxed);
            Err(FreshVarError)
        } else if OVERFLOWED.load(atomic::Ordering::Relaxed) {
            Err(FreshVarError)
        } else {
            Ok(IVar::from(QualIdentifier::from(format!("@{}", x).as_str())))
        }
    }

    pub(crate) fn process<T>(&mut self, command: &Command<T>) {
        use Command::*;
        match command {
            DeclareSort { symbol, arity } => self.declare_sort(symbol.clone(), arity.clone()),
            DeclareFun {
                symbol,
                parameters,
                sort,
            } => self.declare_fun(symbol.clone(), parameters.clone(), sort.clone()),
            DeclareConst { symbol, sort } => self.declare_const(symbol.clone(), sort.clone()),
            _ => (),
        }
    }

    fn declare_sort(&mut self, symbol: ISymbol, arity: Numeral) {
        let sorts = &mut self.script.sorts;
        sorts.entry(symbol).or_insert(SortSignature { arity });
    }

    fn declare_fun(&mut self, symbol: ISymbol, params: Vec<ISort>, return_type: ISort) {
        let funs = &mut self.script.funs;
        funs.entry(symbol).or_insert(FunctionSignature {
            params,
            return_type,
        });
    }

    fn declare_const(&mut self, symbol: ISymbol, ty: ISort) {
        self.declare_fun(symbol, vec![], ty)
    }

    /// Determines the return type/sort of the function denoted by `sym`.
    pub fn return_sort(&self, sym: &ISymbol) -> Option<&ISort> {
        self.script.funs.get(sym).map(|sig| &sig.return_type)
    }

    /// Determines the type/sort of the constant denoted by `sym`.
    /// Since constants are just nullary functions, this is equivalent to [`Self::return_sort`].
    pub fn const_sort(&self, sym: &ISymbol) -> Option<&ISort> {
        self.return_sort(sym)
    }
}

impl LocalCtx {
    /// Marks that a variable is bound, returning the old sort of the symbol if it was previously bound.
    pub(crate) fn bind_var(&mut self, sym: ISymbol, sort: Option<ISort>) -> Option<Option<ISort>> {
        self.bound_vars.insert(sym, sort)
    }

    /// Marks that a variable is no longer bound.
    pub(crate) fn unbind_var(&mut self, sym: &ISymbol) {
        self.bound_vars.remove(sym);
    }

    pub(crate) fn is_bound(&self, sym: &ISymbol) -> bool {
        self.bound_vars.get(sym).is_some()
    }

    pub(crate) fn is_free(&self, sym: &ISymbol) -> bool {
        !self.is_bound(sym)
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct SortSignature {
    arity: Numeral,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct FunctionSignature {
    params: Vec<ISort>,
    return_type: ISort,
}
