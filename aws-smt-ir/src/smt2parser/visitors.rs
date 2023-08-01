// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

// Modifications: Copyright (c) Amazon.com, Inc. or its affiliates. All Rights Reserved.

//! The visiting traits expected by the SMT2 parser.

use crate::smt2parser::{Binary, Decimal, Hexadecimal, Numeral};
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use strum::EnumIter;

pub trait ConstantVisitor {
    type T;
    type E;

    fn visit_numeral_constant(&mut self, value: Numeral) -> Result<Self::T, Self::E>;
    fn visit_decimal_constant(&mut self, value: Decimal) -> Result<Self::T, Self::E>;
    fn visit_hexadecimal_constant(&mut self, value: Hexadecimal) -> Result<Self::T, Self::E>;
    fn visit_binary_constant(&mut self, value: Binary) -> Result<Self::T, Self::E>;
    fn visit_string_constant(&mut self, value: String) -> Result<Self::T, Self::E>;
}

#[derive(Debug, Clone, Copy, PartialOrd, PartialEq, Ord, Eq, Hash, EnumIter)]
pub enum SymbolKind {
    Unknown,
    Variable,
    Constant,
    Function,
    Sort,
    Datatype,
    TypeVar,
    Constructor,
    Selector,
}

pub trait SymbolVisitor {
    type T;
    type E;

    fn visit_fresh_symbol(&mut self, value: String, kind: SymbolKind) -> Result<Self::T, Self::E>;

    fn visit_bound_symbol(&mut self, value: String) -> Result<Self::T, Self::E> {
        self.visit_fresh_symbol(value, SymbolKind::Unknown)
    }

    // If the symbol is not a valid bound symbol, try to create a fresh one.
    fn visit_any_symbol(&mut self, value: String) -> Result<Self::T, Self::E> {
        self.visit_bound_symbol(value.clone())
            .or_else(|_| self.visit_fresh_symbol(value, SymbolKind::Unknown))
    }

    fn bind_symbol(&mut self, _symbol: &Self::T) {}

    fn unbind_symbol(&mut self, _symbol: &Self::T) {}
}

pub trait KeywordVisitor {
    type T;
    type E;

    fn visit_keyword(&mut self, value: String) -> Result<Self::T, Self::E>;
}

pub trait SExprVisitor<Constant, Symbol, Keyword> {
    type T;
    type E;

    fn visit_constant_s_expr(&mut self, value: Constant) -> Result<Self::T, Self::E>;
    fn visit_symbol_s_expr(&mut self, value: Symbol) -> Result<Self::T, Self::E>;
    fn visit_keyword_s_expr(&mut self, value: Keyword) -> Result<Self::T, Self::E>;
    fn visit_application_s_expr(&mut self, values: Vec<Self::T>) -> Result<Self::T, Self::E>;
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum Index<Symbol = crate::smt2parser::concrete::Symbol> {
    Numeral(Numeral),
    Symbol(Symbol),
}

impl<S> Index<S> {
    /// Remap the symbols of an Index value.
    pub(crate) fn remap<F, V, T, E>(self, v: &mut V, f: F) -> Result<Index<T>, E>
    where
        F: Copy + Fn(&mut V, S) -> Result<T, E>,
    {
        use Index::*;
        match self {
            Numeral(n) => Ok(Numeral(n)),
            Symbol(s) => Ok(Symbol(f(v, s)?)),
        }
    }
}

/// Concrete identifier.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum Identifier<Symbol = crate::smt2parser::concrete::Symbol> {
    Simple {
        symbol: Symbol,
    },
    Indexed {
        symbol: Symbol,
        indices: Vec<Index<Symbol>>,
    },
}

impl<S> Identifier<S> {
    /// Remap the symbols of an Identifier value.
    pub(crate) fn remap<F, V, T, E>(self, v: &mut V, f: F) -> Result<Identifier<T>, E>
    where
        F: Copy + Fn(&mut V, S) -> Result<T, E>,
    {
        use Identifier::*;
        match self {
            Simple { symbol } => Ok(Simple {
                symbol: f(v, symbol)?,
            }),
            Indexed { symbol, indices } => Ok(Indexed {
                symbol: f(v, symbol)?,
                indices: indices
                    .into_iter()
                    .map(|i| i.remap(v, f))
                    .collect::<Result<_, E>>()?,
            }),
        }
    }
}

pub trait SortVisitor<Symbol> {
    type T;
    type E;

    fn visit_simple_sort(&mut self, identifier: Identifier<Symbol>) -> Result<Self::T, Self::E>;
    fn visit_parameterized_sort(
        &mut self,
        identifier: Identifier<Symbol>,
        parameters: Vec<Self::T>,
    ) -> Result<Self::T, Self::E>;
}

pub trait QualIdentifierVisitor<Identifier, Sort> {
    type T;
    type E;

    fn visit_simple_identifier(&mut self, identifier: Identifier) -> Result<Self::T, Self::E>;
    fn visit_sorted_identifier(
        &mut self,
        identifier: Identifier,
        sort: Sort,
    ) -> Result<Self::T, Self::E>;
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum AttributeValue<
    Constant = crate::smt2parser::concrete::Constant,
    Symbol = crate::smt2parser::concrete::Symbol,
    SExpr = crate::smt2parser::concrete::SExpr,
> {
    None,
    Constant(Constant),
    Symbol(Symbol),
    SExpr(Vec<SExpr>),
}

impl<T1, T2, T3> AttributeValue<T1, T2, T3> {
    /// Remap the generically-typed values of an AttributeValue.
    pub(crate) fn remap<V, F1, F2, F3, R1, R2, R3, E>(
        self,
        v: &mut V,
        fcst: F1,
        fsym: F2,
        fsexp: F3,
    ) -> Result<AttributeValue<R1, R2, R3>, E>
    where
        F1: Fn(&mut V, T1) -> Result<R1, E>,
        F2: Fn(&mut V, T2) -> Result<R2, E>,
        F3: Fn(&mut V, T3) -> Result<R3, E>,
    {
        use AttributeValue::*;
        let value = match self {
            None => None,
            Constant(value) => Constant(fcst(v, value)?),
            Symbol(value) => Symbol(fsym(v, value)?),
            SExpr(values) => SExpr(
                values
                    .into_iter()
                    .map(|x| fsexp(v, x))
                    .collect::<Result<_, E>>()?,
            ),
        };
        Ok(value)
    }
}

pub trait TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort> {
    type T;
    type E;

    fn visit_constant(&mut self, constant: Constant) -> Result<Self::T, Self::E>;

    fn visit_qual_identifier(
        &mut self,
        qual_identifier: QualIdentifier,
    ) -> Result<Self::T, Self::E>;

    fn visit_application(
        &mut self,
        qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Result<Self::T, Self::E>;

    fn visit_let(
        &mut self,
        var_bindings: Vec<(Symbol, Self::T)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E>;

    fn visit_forall(
        &mut self,
        vars: Vec<(Symbol, Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E>;

    fn visit_exists(
        &mut self,
        vars: Vec<(Symbol, Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E>;

    fn visit_match(
        &mut self,
        term: Self::T,
        cases: Vec<(Vec<Symbol>, Self::T)>,
    ) -> Result<Self::T, Self::E>;

    fn visit_attributes(
        &mut self,
        term: Self::T,
        attributes: Vec<(Keyword, AttributeValue<Constant, Symbol, SExpr>)>,
    ) -> Result<Self::T, Self::E>;
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct ConstructorDec<Symbol, Sort> {
    pub symbol: Symbol,
    pub selectors: Vec<(Symbol, Sort)>,
}

impl<T1, T2> ConstructorDec<T1, T2> {
    /// Remap the generically-typed values of a ConstructorDec value.
    /// Note: Constructor symbols and selector symbols are remapped using distinct function `fcons` and `fsel`.
    pub(crate) fn remap<V, F1, F2, F3, R1, R2, E>(
        self,
        v: &mut V,
        fcons: F1,
        fsel: F2,
        fsort: F3,
    ) -> Result<ConstructorDec<R1, R2>, E>
    where
        F1: Fn(&mut V, T1) -> Result<R1, E>,
        F2: Fn(&mut V, T1) -> Result<R1, E>,
        F3: Fn(&mut V, T2) -> Result<R2, E>,
    {
        Ok(ConstructorDec {
            symbol: fcons(v, self.symbol)?,
            selectors: self
                .selectors
                .into_iter()
                .map(|(s1, s2)| Ok((fsel(v, s1)?, fsort(v, s2)?)))
                .collect::<Result<_, E>>()?,
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct DatatypeDec<Symbol = crate::smt2parser::concrete::Symbol, Sort = crate::smt2parser::concrete::Sort> {
    pub parameters: Vec<Symbol>,
    pub constructors: Vec<ConstructorDec<Symbol, Sort>>,
}

impl<T1, T2> DatatypeDec<T1, T2> {
    /// Remap the generically-typed values of a DatatypeDec value.
    pub(crate) fn remap<V, F1, F2, F3, F4, R1, R2, E>(
        self,
        v: &mut V,
        fpar: F1,
        fcons: F2,
        fsel: F3,
        fsort: F4,
    ) -> Result<DatatypeDec<R1, R2>, E>
    where
        F1: Copy + Fn(&mut V, T1) -> Result<R1, E>,
        F2: Copy + Fn(&mut V, T1) -> Result<R1, E>,
        F3: Copy + Fn(&mut V, T1) -> Result<R1, E>,
        F4: Copy + Fn(&mut V, T2) -> Result<R2, E>,
    {
        Ok(DatatypeDec {
            parameters: self
                .parameters
                .into_iter()
                .map(|x| fpar(v, x))
                .collect::<Result<_, E>>()?,
            constructors: self
                .constructors
                .into_iter()
                .map(|c| c.remap(v, fcons, fsel, fsort))
                .collect::<Result<_, E>>()?,
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct FunctionDec<Symbol = crate::smt2parser::concrete::Symbol, Sort = crate::smt2parser::concrete::Sort> {
    pub name: Symbol,
    pub parameters: Vec<(Symbol, Sort)>,
    pub result: Sort,
}

impl<T1, T2> FunctionDec<T1, T2> {
    /// Remap the generically-typed values of a FunctionDec value.
    pub(crate) fn remap<V, F1, F2, F3, R1, R2, E>(
        self,
        v: &mut V,
        ffun: F1,
        fvar: F2,
        fsort: F3,
    ) -> Result<FunctionDec<R1, R2>, E>
    where
        F1: Copy + Fn(&mut V, T1) -> Result<R1, E>,
        F2: Copy + Fn(&mut V, T1) -> Result<R1, E>,
        F3: Copy + Fn(&mut V, T2) -> Result<R2, E>,
    {
        Ok(FunctionDec {
            name: ffun(v, self.name)?,
            parameters: self
                .parameters
                .into_iter()
                .map(|(s1, s2)| Ok((fvar(v, s1)?, fsort(v, s2)?)))
                .collect::<Result<_, E>>()?,
            result: fsort(v, self.result)?,
        })
    }
}

pub trait CommandVisitor<Term, Symbol, Sort, Keyword, Constant, SExpr> {
    type T;
    type E;

    fn visit_assert(&mut self, term: Term) -> Result<Self::T, Self::E>;

    fn visit_check_sat(&mut self) -> Result<Self::T, Self::E>;

    fn visit_check_sat_assuming(
        &mut self,
        literals: Vec<(Symbol, bool)>,
    ) -> Result<Self::T, Self::E>;

    fn visit_declare_const(&mut self, symbol: Symbol, sort: Sort) -> Result<Self::T, Self::E>;

    fn visit_declare_datatype(
        &mut self,
        symbol: Symbol,
        datatype: DatatypeDec<Symbol, Sort>,
    ) -> Result<Self::T, Self::E>;

    fn visit_declare_datatypes(
        &mut self,
        datatypes: Vec<(Symbol, Numeral, DatatypeDec<Symbol, Sort>)>,
    ) -> Result<Self::T, Self::E>;

    fn visit_declare_fun(
        &mut self,
        symbol: Symbol,
        parameters: Vec<Sort>,
        sort: Sort,
    ) -> Result<Self::T, Self::E>;

    fn visit_declare_sort(&mut self, symbol: Symbol, arity: Numeral) -> Result<Self::T, Self::E>;

    fn visit_define_fun(
        &mut self,
        sig: FunctionDec<Symbol, Sort>,
        term: Term,
    ) -> Result<Self::T, Self::E>;

    fn visit_define_fun_rec(
        &mut self,
        sig: FunctionDec<Symbol, Sort>,
        term: Term,
    ) -> Result<Self::T, Self::E>;

    fn visit_define_funs_rec(
        &mut self,
        funs: Vec<(FunctionDec<Symbol, Sort>, Term)>,
    ) -> Result<Self::T, Self::E>;

    fn visit_define_sort(
        &mut self,
        symbol: Symbol,
        parameters: Vec<Symbol>,
        sort: Sort,
    ) -> Result<Self::T, Self::E>;

    fn visit_echo(&mut self, message: String) -> Result<Self::T, Self::E>;

    fn visit_exit(&mut self) -> Result<Self::T, Self::E>;

    fn visit_get_assertions(&mut self) -> Result<Self::T, Self::E>;

    fn visit_get_assignment(&mut self) -> Result<Self::T, Self::E>;

    fn visit_get_info(&mut self, flag: Keyword) -> Result<Self::T, Self::E>;

    fn visit_get_model(&mut self) -> Result<Self::T, Self::E>;

    fn visit_get_option(&mut self, keyword: Keyword) -> Result<Self::T, Self::E>;

    fn visit_get_proof(&mut self) -> Result<Self::T, Self::E>;

    fn visit_get_unsat_assumptions(&mut self) -> Result<Self::T, Self::E>;

    fn visit_get_unsat_core(&mut self) -> Result<Self::T, Self::E>;

    fn visit_get_value(&mut self, terms: Vec<Term>) -> Result<Self::T, Self::E>;

    fn visit_pop(&mut self, level: Numeral) -> Result<Self::T, Self::E>;

    fn visit_push(&mut self, level: Numeral) -> Result<Self::T, Self::E>;

    fn visit_reset(&mut self) -> Result<Self::T, Self::E>;

    fn visit_reset_assertions(&mut self) -> Result<Self::T, Self::E>;

    fn visit_set_info(
        &mut self,
        keyword: Keyword,
        value: AttributeValue<Constant, Symbol, SExpr>,
    ) -> Result<Self::T, Self::E>;

    fn visit_set_logic(&mut self, symbol: Symbol) -> Result<Self::T, Self::E>;

    fn visit_set_option(
        &mut self,
        keyword: Keyword,
        value: AttributeValue<Constant, Symbol, SExpr>,
    ) -> Result<Self::T, Self::E>;
}

/// A visitor for the entire SMT2 syntax.
pub trait Smt2Visitor:
    ConstantVisitor<T = <Self as Smt2Visitor>::Constant, E = <Self as Smt2Visitor>::Error>
    + SymbolVisitor<T = <Self as Smt2Visitor>::Symbol, E = <Self as Smt2Visitor>::Error>
    + KeywordVisitor<T = <Self as Smt2Visitor>::Keyword, E = <Self as Smt2Visitor>::Error>
    + SExprVisitor<
        <Self as Smt2Visitor>::Constant,
        <Self as Smt2Visitor>::Symbol,
        <Self as Smt2Visitor>::Keyword,
        T = <Self as Smt2Visitor>::SExpr,
        E = <Self as Smt2Visitor>::Error,
    > + QualIdentifierVisitor<
        Identifier<<Self as Smt2Visitor>::Symbol>,
        <Self as Smt2Visitor>::Sort,
        T = <Self as Smt2Visitor>::QualIdentifier,
        E = <Self as Smt2Visitor>::Error,
    > + SortVisitor<
        <Self as Smt2Visitor>::Symbol,
        T = <Self as Smt2Visitor>::Sort,
        E = <Self as Smt2Visitor>::Error,
    > + TermVisitor<
        <Self as Smt2Visitor>::Constant,
        <Self as Smt2Visitor>::QualIdentifier,
        <Self as Smt2Visitor>::Keyword,
        <Self as Smt2Visitor>::SExpr,
        <Self as Smt2Visitor>::Symbol,
        <Self as Smt2Visitor>::Sort,
        T = <Self as Smt2Visitor>::Term,
        E = <Self as Smt2Visitor>::Error,
    > + CommandVisitor<
        <Self as Smt2Visitor>::Term,
        <Self as Smt2Visitor>::Symbol,
        <Self as Smt2Visitor>::Sort,
        <Self as Smt2Visitor>::Keyword,
        <Self as Smt2Visitor>::Constant,
        <Self as Smt2Visitor>::SExpr,
        T = <Self as Smt2Visitor>::Command,
        E = <Self as Smt2Visitor>::Error,
    >
{
    type Error;
    type Constant;
    type QualIdentifier;
    type Keyword;
    type Sort;
    type SExpr;
    type Symbol;
    type Term;
    type Command;

    fn syntax_error(&mut self, position: crate::smt2parser::Position, s: String) -> Self::Error;
    fn parsing_error(&mut self, position: crate::smt2parser::Position, s: String) -> Self::Error;
}

impl<Symbol> std::fmt::Display for Index<Symbol>
where
    Symbol: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨numeral⟩ | ⟨symbol⟩
        match self {
            Index::Numeral(num) => write!(f, "{}", num),
            Index::Symbol(sym) => write!(f, "{}", sym),
        }
    }
}

impl<Symbol> std::fmt::Display for Identifier<Symbol>
where
    Symbol: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨symbol⟩ | ( _ ⟨symbol⟩ ⟨index⟩+ )
        match self {
            Identifier::Simple { symbol } => write!(f, "{}", symbol),
            Identifier::Indexed { symbol, indices } => {
                write!(f, "(_ {} {})", symbol, indices.iter().format(" "))
            }
        }
    }
}

impl<Constant, Symbol, SExpr> std::fmt::Display for AttributeValue<Constant, Symbol, SExpr>
where
    Constant: std::fmt::Display,
    Symbol: std::fmt::Display,
    SExpr: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨spec_constant⟩ | ⟨symbol⟩ | ( ⟨s_expr⟩∗ ) |
        use AttributeValue::*;
        match self {
            None => Ok(()),
            Constant(c) => write!(f, "{}", c),
            Symbol(s) => write!(f, "{}", s),
            SExpr(values) => write!(f, "({})", values.iter().format(" ")),
        }
    }
}

impl<Symbol, Sort> std::fmt::Display for ConstructorDec<Symbol, Sort>
where
    Symbol: std::fmt::Display,
    Sort: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ( ⟨symbol⟩ ⟨selector_dec⟩∗ )
        write!(
            f,
            "({} {})",
            self.symbol,
            self.selectors
                .iter()
                .format_with(" ", |(symbol, sort), f| f(&format_args!(
                    "({} {})",
                    symbol, sort
                )))
        )
    }
}

impl<Symbol, Sort> std::fmt::Display for DatatypeDec<Symbol, Sort>
where
    Symbol: std::fmt::Display,
    Sort: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ( ⟨constructor_dec⟩+ ) | ( par ( ⟨symbol⟩+ ) ( ⟨constructor_dec⟩+ ) )
        if self.parameters.is_empty() {
            write!(f, "({})", self.constructors.iter().format(" "))
        } else {
            let symbols = format!("({})", self.parameters.iter().format(" "));
            let constructors = format!("({})", self.constructors.iter().format(" "));
            write!(f, "(par {} {})", symbols, constructors)
        }
    }
}

impl<Symbol, Sort> std::fmt::Display for FunctionDec<Symbol, Sort>
where
    Symbol: std::fmt::Display,
    Sort: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨symbol⟩ ( ⟨sorted_var⟩∗ ) ⟨sort⟩
        let params = self
            .parameters
            .iter()
            .format_with(" ", |(symbol, sort), f| {
                f(&format_args!("({} {})", symbol, sort))
            });
        write!(f, "{} ({}) {}", self.name, params, self.result)
    }
}
