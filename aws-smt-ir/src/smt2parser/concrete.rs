// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

// Modifications: Copyright (c) Amazon.com, Inc. or its affiliates. All Rights Reserved.

//! A concrete syntax tree together with building functions (aka parser visitors) and SEXP-printing functions.

use crate::smt2parser::{
    lexer,
    visitors::{
        CommandVisitor, ConstantVisitor, KeywordVisitor, QualIdentifierVisitor, SExprVisitor,
        Smt2Visitor, SortVisitor, SymbolKind, SymbolVisitor, TermVisitor,
    },
    Binary, Decimal, Hexadecimal, Numeral, Position,
};
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Concrete syntax for a constant.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum Constant {
    Numeral(Numeral),
    Decimal(Decimal),
    Hexadecimal(Hexadecimal),
    Binary(Binary),
    String(String),
}

/// Concrete symbol.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Ord, PartialOrd, Serialize, Deserialize)]
pub struct Symbol(pub String);

/// Concrete keyword.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Ord, PartialOrd, Serialize, Deserialize)]
pub struct Keyword(pub String);

pub use crate::smt2parser::visitors::Identifier;

/// Concrete syntax for an S-expression.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum SExpr<Constant = self::Constant, Symbol = self::Symbol, Keyword = self::Keyword> {
    Constant(Constant),
    Symbol(Symbol),
    Keyword(Keyword),
    Application(Vec<Self>),
}

pub use crate::smt2parser::visitors::{AttributeValue, DatatypeDec, FunctionDec};

/// Concrete syntax for a sort.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum Sort<Identifier = self::Identifier> {
    Simple {
        identifier: Identifier,
    },
    Parameterized {
        identifier: Identifier,
        parameters: Vec<Self>,
    },
}

/// Concrete syntax for a qualified-identifier.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum QualIdentifier<Identifier = self::Identifier, Sort = self::Sort> {
    Simple { identifier: Identifier },
    Sorted { identifier: Identifier, sort: Sort },
}

/// Concrete syntax for a term.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum Term<
    Constant = self::Constant,
    QualIdentifier = self::QualIdentifier,
    Keyword = self::Keyword,
    SExpr = self::SExpr,
    Symbol = self::Symbol,
    Sort = self::Sort,
> {
    Constant(Constant),
    QualIdentifier(QualIdentifier),
    Application {
        qual_identifier: QualIdentifier,
        arguments: Vec<Self>,
    },
    Let {
        var_bindings: Vec<(Symbol, Self)>,
        term: Box<Self>,
    },
    Forall {
        vars: Vec<(Symbol, Sort)>,
        term: Box<Self>,
    },
    Exists {
        vars: Vec<(Symbol, Sort)>,
        term: Box<Self>,
    },
    Match {
        term: Box<Self>,
        cases: Vec<(Vec<Symbol>, Self)>,
    },
    Attributes {
        term: Box<Self>,
        attributes: Vec<(Keyword, AttributeValue<Constant, Symbol, SExpr>)>,
    },
}

/// Concrete syntax for a command.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum Command<
    Term = self::Term,
    Symbol = self::Symbol,
    Sort = self::Sort,
    Keyword = self::Keyword,
    Constant = self::Constant,
    SExpr = self::SExpr,
> {
    Assert {
        term: Term,
    },
    CheckSat,
    CheckSatAssuming {
        literals: Vec<(Symbol, bool)>,
    },
    DeclareConst {
        symbol: Symbol,
        sort: Sort,
    },
    DeclareDatatype {
        symbol: Symbol,
        datatype: DatatypeDec<Symbol, Sort>,
    },
    DeclareDatatypes {
        datatypes: Vec<(Symbol, Numeral, DatatypeDec<Symbol, Sort>)>,
    },
    DeclareFun {
        symbol: Symbol,
        parameters: Vec<Sort>,
        sort: Sort,
    },
    DeclareSort {
        symbol: Symbol,
        arity: Numeral,
    },
    DefineFun {
        sig: FunctionDec<Symbol, Sort>,
        term: Term,
    },
    DefineFunRec {
        sig: FunctionDec<Symbol, Sort>,
        term: Term,
    },
    DefineFunsRec {
        funs: Vec<(FunctionDec<Symbol, Sort>, Term)>,
    },
    DefineSort {
        symbol: Symbol,
        parameters: Vec<Symbol>,
        sort: Sort,
    },
    Echo {
        message: String,
    },
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo {
        flag: Keyword,
    },
    GetModel,
    GetOption {
        keyword: Keyword,
    },
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue {
        terms: Vec<Term>,
    },
    Pop {
        level: Numeral,
    },
    Push {
        level: Numeral,
    },
    Reset,
    ResetAssertions,
    SetInfo {
        keyword: Keyword,
        value: AttributeValue<Constant, Symbol, SExpr>,
    },
    SetLogic {
        symbol: Symbol,
    },
    SetOption {
        keyword: Keyword,
        value: AttributeValue<Constant, Symbol, SExpr>,
    },
}

/// An implementation of [`Smt2Visitor`] that returns concrete syntax values.
#[derive(Default, Debug, Eq, PartialEq, Clone, Hash, Serialize, Deserialize)]
pub struct SyntaxBuilder;

#[derive(Error, Debug)]
pub enum Error {
    #[error("error: {1}\n   --> {0}")]
    SyntaxError(Position, String),
    #[error("error: {1}\n   --> {0}")]
    ParsingError(Position, String),
}

impl ConstantVisitor for SyntaxBuilder {
    type T = Constant;
    type E = Error;

    fn visit_numeral_constant(&mut self, value: Numeral) -> Result<Self::T, Self::E> {
        Ok(Constant::Numeral(value))
    }
    fn visit_decimal_constant(&mut self, value: Decimal) -> Result<Self::T, Self::E> {
        Ok(Constant::Decimal(value))
    }
    fn visit_hexadecimal_constant(&mut self, value: Hexadecimal) -> Result<Self::T, Self::E> {
        Ok(Constant::Hexadecimal(value))
    }
    fn visit_binary_constant(&mut self, value: Binary) -> Result<Self::T, Self::E> {
        Ok(Constant::Binary(value))
    }
    fn visit_string_constant(&mut self, value: String) -> Result<Self::T, Self::E> {
        Ok(Constant::String(value))
    }
}

impl Constant {
    /// Visit a concrete constant.
    pub fn accept<V>(self, visitor: &mut V) -> Result<V::T, V::E>
    where
        V: ConstantVisitor,
    {
        use Constant::*;
        match self {
            Numeral(value) => visitor.visit_numeral_constant(value),
            Decimal(value) => visitor.visit_decimal_constant(value),
            Hexadecimal(value) => visitor.visit_hexadecimal_constant(value),
            Binary(value) => visitor.visit_binary_constant(value),
            String(value) => visitor.visit_string_constant(value),
        }
    }
}

impl SymbolVisitor for SyntaxBuilder {
    type T = Symbol;
    type E = Error;

    fn visit_fresh_symbol(&mut self, value: String, _kind: SymbolKind) -> Result<Self::T, Self::E> {
        Ok(Symbol(value))
    }
}

impl KeywordVisitor for SyntaxBuilder {
    type T = Keyword;
    type E = Error;

    fn visit_keyword(&mut self, value: String) -> Result<Self::T, Self::E> {
        Ok(Keyword(value))
    }
}

impl Keyword {
    /// Visit a concrete keyword.
    pub fn accept<V>(self, visitor: &mut V) -> Result<V::T, V::E>
    where
        V: KeywordVisitor,
    {
        visitor.visit_keyword(self.0)
    }
}

impl<Constant, Symbol, Keyword> SExprVisitor<Constant, Symbol, Keyword> for SyntaxBuilder {
    type T = SExpr<Constant, Symbol, Keyword>;
    type E = Error;

    fn visit_constant_s_expr(&mut self, value: Constant) -> Result<Self::T, Self::E> {
        Ok(SExpr::Constant(value))
    }

    fn visit_symbol_s_expr(&mut self, value: Symbol) -> Result<Self::T, Self::E> {
        Ok(SExpr::Symbol(value))
    }

    fn visit_keyword_s_expr(&mut self, value: Keyword) -> Result<Self::T, Self::E> {
        Ok(SExpr::Keyword(value))
    }

    fn visit_application_s_expr(&mut self, values: Vec<Self::T>) -> Result<Self::T, Self::E> {
        Ok(SExpr::Application(values))
    }
}

impl SExpr {
    /// Visit a concrete S-expression.
    pub fn accept<V, T, C, S, K, E>(self, visitor: &mut V) -> Result<T, E>
    where
        V: SExprVisitor<C, S, K, T = T, E = E>
            + ConstantVisitor<T = C, E = E>
            + SymbolVisitor<T = S, E = E>
            + KeywordVisitor<T = K, E = E>,
    {
        use SExpr::*;
        match self {
            Constant(value) => {
                let c = value.accept(visitor)?;
                visitor.visit_constant_s_expr(c)
            }
            Symbol(value) => {
                let s = visitor.visit_bound_symbol(value.0)?;
                visitor.visit_symbol_s_expr(s)
            }
            Keyword(value) => {
                let k = value.accept(visitor)?;
                visitor.visit_keyword_s_expr(k)
            }
            Application(values) => {
                let ts = values
                    .into_iter()
                    .map(|e| e.accept(visitor))
                    .collect::<Result<_, E>>()?;
                visitor.visit_application_s_expr(ts)
            }
        }
    }
}

impl<Symbol> SortVisitor<Symbol> for SyntaxBuilder {
    type T = Sort<Identifier<Symbol>>;
    type E = Error;

    fn visit_simple_sort(&mut self, identifier: Identifier<Symbol>) -> Result<Self::T, Self::E> {
        Ok(Sort::Simple { identifier })
    }

    fn visit_parameterized_sort(
        &mut self,
        identifier: Identifier<Symbol>,
        parameters: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        Ok(Sort::Parameterized {
            identifier,
            parameters,
        })
    }
}

impl Sort {
    /// Visit a concrete sort.
    pub fn accept<V, T, S, E>(self, visitor: &mut V) -> Result<T, E>
    where
        V: SortVisitor<S, T = T, E = E> + SymbolVisitor<T = S, E = E>,
    {
        use Sort::*;
        match self {
            Simple { identifier } => {
                let i = identifier.remap(visitor, |v, s: Symbol| v.visit_bound_symbol(s.0))?;
                visitor.visit_simple_sort(i)
            }
            Parameterized {
                identifier,
                parameters,
            } => {
                let i = identifier.remap(visitor, |v, s: Symbol| v.visit_bound_symbol(s.0))?;
                let ts = parameters
                    .into_iter()
                    .map(|s| s.accept(visitor))
                    .collect::<Result<_, E>>()?;
                visitor.visit_parameterized_sort(i, ts)
            }
        }
    }
}

impl<Identifier, Sort> QualIdentifierVisitor<Identifier, Sort> for SyntaxBuilder {
    type T = QualIdentifier<Identifier, Sort>;
    type E = Error;

    fn visit_simple_identifier(&mut self, identifier: Identifier) -> Result<Self::T, Self::E> {
        Ok(QualIdentifier::Simple { identifier })
    }

    fn visit_sorted_identifier(
        &mut self,
        identifier: Identifier,
        sort: Sort,
    ) -> Result<Self::T, Self::E> {
        Ok(QualIdentifier::Sorted { identifier, sort })
    }
}

impl QualIdentifier {
    /// Visit a concrete qualified identifier.
    pub fn accept<V, T, E, S1, S2>(self, visitor: &mut V) -> Result<T, E>
    where
        V: SortVisitor<S1, T = S2, E = E>
            + SymbolVisitor<T = S1, E = E>
            + QualIdentifierVisitor<Identifier<S1>, S2, T = T, E = E>,
    {
        use QualIdentifier::*;
        match self {
            Simple { identifier } => {
                let i = identifier.remap(visitor, |v, s: Symbol| v.visit_bound_symbol(s.0))?;
                visitor.visit_simple_identifier(i)
            }
            Sorted { identifier, sort } => {
                let i = identifier.remap(visitor, |v, s: Symbol| v.visit_bound_symbol(s.0))?;
                let s = sort.accept(visitor)?;
                visitor.visit_sorted_identifier(i, s)
            }
        }
    }
}

impl<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort>
    TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort> for SyntaxBuilder
{
    type T = Term<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort>;
    type E = Error;

    fn visit_constant(&mut self, constant: Constant) -> Result<Self::T, Self::E> {
        Ok(Term::Constant(constant))
    }

    fn visit_qual_identifier(
        &mut self,
        qual_identifier: QualIdentifier,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::QualIdentifier(qual_identifier))
    }

    fn visit_application(
        &mut self,
        qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::Application {
            qual_identifier,
            arguments,
        })
    }

    fn visit_let(
        &mut self,
        var_bindings: Vec<(Symbol, Self::T)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        let term = Box::new(term);
        Ok(Term::Let { var_bindings, term })
    }

    fn visit_forall(
        &mut self,
        vars: Vec<(Symbol, Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        let term = Box::new(term);
        Ok(Term::Forall { vars, term })
    }

    fn visit_exists(
        &mut self,
        vars: Vec<(Symbol, Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        let term = Box::new(term);
        Ok(Term::Exists { vars, term })
    }

    fn visit_match(
        &mut self,
        term: Self::T,
        cases: Vec<(Vec<Symbol>, Self::T)>,
    ) -> Result<Self::T, Self::E> {
        let term = Box::new(term);
        Ok(Term::Match { term, cases })
    }

    fn visit_attributes(
        &mut self,
        term: Self::T,
        attributes: Vec<(Keyword, AttributeValue<Constant, Symbol, SExpr>)>,
    ) -> Result<Self::T, Self::E> {
        let term = Box::new(term);
        Ok(Term::Attributes { term, attributes })
    }
}

impl Term {
    /// Visit a concrete term.
    pub fn accept<V, T, E, S1, S2, S3, S4, S5, S6>(self, visitor: &mut V) -> Result<T, E>
    where
        V: SortVisitor<S1, T = S2, E = E>
            + SymbolVisitor<T = S1, E = E>
            + QualIdentifierVisitor<Identifier<S1>, S2, T = S3, E = E>
            + ConstantVisitor<T = S4, E = E>
            + KeywordVisitor<T = S5, E = E>
            + SExprVisitor<S4, S1, S5, T = S6, E = E>
            + TermVisitor<S4, S3, S5, S6, S1, S2, T = T, E = E>,
    {
        use Term::*;
        match self {
            Constant(value) => {
                let c = value.accept(visitor)?;
                visitor.visit_constant(c)
            }
            QualIdentifier(value) => {
                let qi = value.accept(visitor)?;
                visitor.visit_qual_identifier(qi)
            }
            Application {
                qual_identifier,
                arguments,
            } => {
                let qi = qual_identifier.accept(visitor)?;
                let mut ts = Vec::new();
                for t in arguments {
                    ts.push(t.accept(visitor)?);
                }
                visitor.visit_application(qi, ts)
            }
            Let { var_bindings, term } => {
                let bs = var_bindings
                    .into_iter()
                    .map(|(s, t)| {
                        Ok((
                            visitor.visit_fresh_symbol(s.0, SymbolKind::Variable)?,
                            t.accept(visitor)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, E>>()?;
                bs.iter().for_each(|(s, _)| visitor.bind_symbol(s));
                let t = term.accept(visitor)?;
                bs.iter().for_each(|(s, _)| visitor.unbind_symbol(s));
                visitor.visit_let(bs, t)
            }
            Forall { vars, term } => {
                let vs = vars
                    .into_iter()
                    .map(|(v, s)| {
                        Ok((
                            visitor.visit_fresh_symbol(v.0, SymbolKind::Variable)?,
                            s.accept(visitor)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, E>>()?;
                vs.iter().for_each(|(s, _)| visitor.bind_symbol(s));
                let t = term.accept(visitor)?;
                vs.iter().for_each(|(s, _)| visitor.unbind_symbol(s));
                visitor.visit_forall(vs, t)
            }
            Exists { vars, term } => {
                let vs = vars
                    .into_iter()
                    .map(|(v, s)| {
                        Ok((
                            visitor.visit_fresh_symbol(v.0, SymbolKind::Variable)?,
                            s.accept(visitor)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, E>>()?;
                vs.iter().for_each(|(s, _)| visitor.bind_symbol(s));
                let t = term.accept(visitor)?;
                vs.iter().for_each(|(s, _)| visitor.unbind_symbol(s));
                visitor.visit_exists(vs, t)
            }
            Match { term, cases } => {
                let t = term.accept(visitor)?;
                let cs = cases
                    .into_iter()
                    .map(|(ss, t)| {
                        let mut symbols = Vec::new();
                        let mut ss = ss.into_iter();
                        let mut has_fresh_first_symbol = false;
                        if let Some(s) = ss.next() {
                            // First symbol may be a constructor.
                            symbols.push(visitor.visit_bound_symbol(s.0.clone()).or_else(
                                |_| {
                                    has_fresh_first_symbol = true;
                                    let s = visitor
                                        .visit_fresh_symbol(s.0.clone(), SymbolKind::Variable)?;
                                    visitor.bind_symbol(&s);
                                    Ok(s)
                                },
                            )?);
                        }
                        for s in ss {
                            let s = visitor.visit_fresh_symbol(s.0, SymbolKind::Variable)?;
                            visitor.bind_symbol(&s);
                            symbols.push(s);
                        }
                        let term = t.accept(visitor)?;
                        let mut ss = symbols.iter();
                        if let Some(s) = ss.next() {
                            if has_fresh_first_symbol {
                                visitor.unbind_symbol(s);
                            }
                        }
                        for s in ss {
                            visitor.unbind_symbol(s);
                        }
                        Ok((symbols, term))
                    })
                    .collect::<Result<_, E>>()?;
                visitor.visit_match(t, cs)
            }
            Attributes { term, attributes } => {
                let t = term.accept(visitor)?;
                let xs = attributes
                    .into_iter()
                    .map(|(k, x)| {
                        Ok((
                            k.accept(visitor)?,
                            x.remap(
                                visitor,
                                |v, c: self::Constant| c.accept(v),
                                |v, s: Symbol| v.visit_bound_symbol(s.0),
                                |v, e: SExpr| e.accept(v),
                            )?,
                        ))
                    })
                    .collect::<Result<_, E>>()?;
                visitor.visit_attributes(t, xs)
            }
        }
    }
}

impl<Term, Symbol, Sort, Keyword, Constant, SExpr>
    CommandVisitor<Term, Symbol, Sort, Keyword, Constant, SExpr> for SyntaxBuilder
{
    type T = Command<Term, Symbol, Sort, Keyword, Constant, SExpr>;
    type E = Error;

    fn visit_assert(&mut self, term: Term) -> Result<Self::T, Self::E> {
        Ok(Command::Assert { term })
    }

    fn visit_check_sat(&mut self) -> Result<Self::T, Self::E> {
        Ok(Command::CheckSat)
    }

    fn visit_check_sat_assuming(
        &mut self,
        literals: Vec<(Symbol, bool)>,
    ) -> Result<Self::T, Self::E> {
        Ok(Command::CheckSatAssuming { literals })
    }

    fn visit_declare_const(&mut self, symbol: Symbol, sort: Sort) -> Result<Self::T, Self::E> {
        Ok(Command::DeclareConst { symbol, sort })
    }

    fn visit_declare_datatype(
        &mut self,
        symbol: Symbol,
        datatype: DatatypeDec<Symbol, Sort>,
    ) -> Result<Self::T, Self::E> {
        Ok(Command::DeclareDatatype { symbol, datatype })
    }

    fn visit_declare_datatypes(
        &mut self,
        datatypes: Vec<(Symbol, Numeral, DatatypeDec<Symbol, Sort>)>,
    ) -> Result<Self::T, Self::E> {
        Ok(Command::DeclareDatatypes { datatypes })
    }

    fn visit_declare_fun(
        &mut self,
        symbol: Symbol,
        parameters: Vec<Sort>,
        sort: Sort,
    ) -> Result<Self::T, Self::E> {
        Ok(Command::DeclareFun {
            symbol,
            parameters,
            sort,
        })
    }

    fn visit_declare_sort(&mut self, symbol: Symbol, arity: Numeral) -> Result<Self::T, Self::E> {
        Ok(Command::DeclareSort { symbol, arity })
    }

    fn visit_define_fun(
        &mut self,
        sig: FunctionDec<Symbol, Sort>,
        term: Term,
    ) -> Result<Self::T, Self::E> {
        Ok(Command::DefineFun { sig, term })
    }

    fn visit_define_fun_rec(
        &mut self,
        sig: FunctionDec<Symbol, Sort>,
        term: Term,
    ) -> Result<Self::T, Self::E> {
        Ok(Command::DefineFunRec { sig, term })
    }

    fn visit_define_funs_rec(
        &mut self,
        funs: Vec<(FunctionDec<Symbol, Sort>, Term)>,
    ) -> Result<Self::T, Self::E> {
        Ok(Command::DefineFunsRec { funs })
    }

    fn visit_define_sort(
        &mut self,
        symbol: Symbol,
        parameters: Vec<Symbol>,
        sort: Sort,
    ) -> Result<Self::T, Self::E> {
        Ok(Command::DefineSort {
            symbol,
            parameters,
            sort,
        })
    }

    fn visit_echo(&mut self, message: String) -> Result<Self::T, Self::E> {
        Ok(Command::Echo { message })
    }

    fn visit_exit(&mut self) -> Result<Self::T, Self::E> {
        Ok(Command::Exit)
    }

    fn visit_get_assertions(&mut self) -> Result<Self::T, Self::E> {
        Ok(Command::GetAssertions)
    }

    fn visit_get_assignment(&mut self) -> Result<Self::T, Self::E> {
        Ok(Command::GetAssignment)
    }

    fn visit_get_info(&mut self, flag: Keyword) -> Result<Self::T, Self::E> {
        Ok(Command::GetInfo { flag })
    }

    fn visit_get_model(&mut self) -> Result<Self::T, Self::E> {
        Ok(Command::GetModel)
    }

    fn visit_get_option(&mut self, keyword: Keyword) -> Result<Self::T, Self::E> {
        Ok(Command::GetOption { keyword })
    }

    fn visit_get_proof(&mut self) -> Result<Self::T, Self::E> {
        Ok(Command::GetProof)
    }

    fn visit_get_unsat_assumptions(&mut self) -> Result<Self::T, Self::E> {
        Ok(Command::GetUnsatAssumptions)
    }

    fn visit_get_unsat_core(&mut self) -> Result<Self::T, Self::E> {
        Ok(Command::GetUnsatCore)
    }

    fn visit_get_value(&mut self, terms: Vec<Term>) -> Result<Self::T, Self::E> {
        Ok(Command::GetValue { terms })
    }

    fn visit_pop(&mut self, level: Numeral) -> Result<Self::T, Self::E> {
        Ok(Command::Pop { level })
    }

    fn visit_push(&mut self, level: Numeral) -> Result<Self::T, Self::E> {
        Ok(Command::Push { level })
    }

    fn visit_reset(&mut self) -> Result<Self::T, Self::E> {
        Ok(Command::Reset)
    }

    fn visit_reset_assertions(&mut self) -> Result<Self::T, Self::E> {
        Ok(Command::ResetAssertions)
    }

    fn visit_set_info(
        &mut self,
        keyword: Keyword,
        value: AttributeValue<Constant, Symbol, SExpr>,
    ) -> Result<Self::T, Self::E> {
        Ok(Command::SetInfo { keyword, value })
    }

    fn visit_set_logic(&mut self, symbol: Symbol) -> Result<Self::T, Self::E> {
        Ok(Command::SetLogic { symbol })
    }

    fn visit_set_option(
        &mut self,
        keyword: Keyword,
        value: AttributeValue<Constant, Symbol, SExpr>,
    ) -> Result<Self::T, Self::E> {
        Ok(Command::SetOption { keyword, value })
    }
}

impl Command {
    /// Visit a concrete command.
    pub fn accept<V, T, E, S1, S2, S3, S4, S5, S6, S7>(self, visitor: &mut V) -> Result<T, E>
    where
        V: SortVisitor<S1, T = S2, E = E>
            + SymbolVisitor<T = S1, E = E>
            + QualIdentifierVisitor<Identifier<S1>, S2, T = S3, E = E>
            + ConstantVisitor<T = S4, E = E>
            + KeywordVisitor<T = S5, E = E>
            + SExprVisitor<S4, S1, S5, T = S6, E = E>
            + TermVisitor<S4, S3, S5, S6, S1, S2, T = S7, E = E>
            + CommandVisitor<S7, S1, S2, S5, S4, S6, T = T, E = E>,
    {
        use Command::*;
        match self {
            Assert { term } => {
                let t = term.accept(visitor)?;
                visitor.visit_assert(t)
            }
            CheckSat => visitor.visit_check_sat(),
            CheckSatAssuming { literals } => {
                let ls = literals
                    .into_iter()
                    .map(|(s, b)| Ok((visitor.visit_bound_symbol(s.0)?, b)))
                    .collect::<Result<_, E>>()?;
                visitor.visit_check_sat_assuming(ls)
            }
            DeclareConst { symbol, sort } => {
                let symb = visitor.visit_fresh_symbol(symbol.0, SymbolKind::Constant)?;
                let sort = sort.accept(visitor)?;
                visitor.bind_symbol(&symb);
                visitor.visit_declare_const(symb, sort)
            }
            DeclareDatatype { symbol, datatype } => {
                let s = visitor.visit_fresh_symbol(symbol.0, SymbolKind::Datatype)?;
                // Datatype may be recursive, so we bind the name early.
                visitor.bind_symbol(&s);
                let dt = datatype.remap(
                    visitor,
                    |_, _| panic!("unexpected type parameters in DeclareDatatype"),
                    |v, s| v.visit_fresh_symbol(s.0, SymbolKind::Constructor),
                    |v, s| v.visit_fresh_symbol(s.0, SymbolKind::Selector),
                    |v, sort| sort.accept(v),
                )?;
                // Bind constructor symbols and selectors.
                dt.constructors.iter().for_each(|c| {
                    visitor.bind_symbol(&c.symbol);
                    c.selectors.iter().for_each(|(s, _)| visitor.bind_symbol(s));
                });
                visitor.visit_declare_datatype(s, dt)
            }
            DeclareDatatypes { datatypes } => {
                let dts = datatypes
                    .into_iter()
                    .map(|(s, n, dt)| {
                        let s = visitor.visit_fresh_symbol(s.0, SymbolKind::Datatype)?;
                        // Datatype may be recursive, so we bind the names early.
                        visitor.bind_symbol(&s);
                        Ok((s, n, dt))
                    })
                    .collect::<Result<Vec<_>, E>>()?;
                let dts = dts
                    .into_iter()
                    .map(|(s, n, dt)| {
                        let dt = dt.remap(
                            visitor,
                            |v, s| {
                                // Bind type parameters before visiting sorts.
                                let s = v.visit_fresh_symbol(s.0, SymbolKind::TypeVar)?;
                                v.bind_symbol(&s);
                                Ok(s)
                            },
                            |v, s| v.visit_fresh_symbol(s.0, SymbolKind::Constructor),
                            |v, s| v.visit_fresh_symbol(s.0, SymbolKind::Selector),
                            |v, sort| sort.accept(v),
                        )?;
                        // Unbind type parameters.
                        dt.parameters.iter().for_each(|s| visitor.unbind_symbol(s));
                        // Bind constructor symbols and selectors.
                        dt.constructors.iter().for_each(|c| {
                            visitor.bind_symbol(&c.symbol);
                            c.selectors.iter().for_each(|(s, _)| visitor.bind_symbol(s));
                        });
                        Ok((s, n, dt))
                    })
                    .collect::<Result<_, E>>()?;
                visitor.visit_declare_datatypes(dts)
            }
            DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                let symb = visitor.visit_fresh_symbol(symbol.0, SymbolKind::Function)?;
                let ps = parameters
                    .into_iter()
                    .map(|s| s.accept(visitor))
                    .collect::<Result<_, E>>()?;
                let sort = sort.accept(visitor)?;
                visitor.bind_symbol(&symb);
                visitor.visit_declare_fun(symb, ps, sort)
            }
            DeclareSort { symbol, arity } => {
                let s = visitor.visit_fresh_symbol(symbol.0, SymbolKind::Sort)?;
                visitor.bind_symbol(&s);
                visitor.visit_declare_sort(s, arity)
            }
            DefineFun { sig, term } => {
                let sig = sig.remap(
                    visitor,
                    |v, s| v.visit_fresh_symbol(s.0, SymbolKind::Function),
                    |v, s| v.visit_fresh_symbol(s.0, SymbolKind::Variable),
                    |v, s| s.accept(v),
                )?;
                sig.parameters
                    .iter()
                    .for_each(|(s, _)| visitor.bind_symbol(s));
                let t = term.accept(visitor)?;
                sig.parameters
                    .iter()
                    .for_each(|(s, _)| visitor.unbind_symbol(s));
                visitor.bind_symbol(&sig.name);
                visitor.visit_define_fun(sig, t)
            }
            DefineFunRec { sig, term } => {
                let sig = sig.remap(
                    visitor,
                    |v, s| v.visit_fresh_symbol(s.0, SymbolKind::Function),
                    |v, s| v.visit_fresh_symbol(s.0, SymbolKind::Variable),
                    |v, s| s.accept(v),
                )?;
                visitor.bind_symbol(&sig.name);
                sig.parameters
                    .iter()
                    .for_each(|(s, _)| visitor.bind_symbol(s));
                let t = term.accept(visitor)?;
                sig.parameters
                    .iter()
                    .for_each(|(s, _)| visitor.unbind_symbol(s));
                visitor.visit_define_fun_rec(sig, t)
            }
            DefineFunsRec { funs } => {
                let funs = funs
                    .into_iter()
                    .map(|(sig, t)| {
                        let sig = sig.remap(
                            visitor,
                            |v, s| v.visit_fresh_symbol(s.0, SymbolKind::Function),
                            |v, s| v.visit_fresh_symbol(s.0, SymbolKind::Variable),
                            |v, s| s.accept(v),
                        )?;
                        visitor.bind_symbol(&sig.name);
                        sig.parameters
                            .iter()
                            .for_each(|(s, _)| visitor.bind_symbol(s));
                        Ok((sig, t))
                    })
                    .collect::<Result<Vec<_>, E>>()?;
                let funs = funs
                    .into_iter()
                    .map(|(sig, t)| {
                        let t = t.accept(visitor)?;
                        sig.parameters
                            .iter()
                            .for_each(|(s, _)| visitor.unbind_symbol(s));
                        Ok((sig, t))
                    })
                    .collect::<Result<_, E>>()?;
                visitor.visit_define_funs_rec(funs)
            }
            DefineSort {
                symbol,
                parameters,
                sort,
            } => {
                let symbol = visitor.visit_fresh_symbol(symbol.0, SymbolKind::Sort)?;
                let ps = parameters
                    .into_iter()
                    .map(|s| visitor.visit_fresh_symbol(s.0, SymbolKind::TypeVar))
                    .collect::<Result<Vec<_>, E>>()?;
                ps.iter().for_each(|s| visitor.bind_symbol(s));
                let sort = sort.accept(visitor)?;
                ps.iter().for_each(|s| visitor.unbind_symbol(s));
                visitor.bind_symbol(&symbol);
                visitor.visit_define_sort(symbol, ps, sort)
            }
            Echo { message } => visitor.visit_echo(message),
            Exit => visitor.visit_exit(),
            GetAssertions => visitor.visit_get_assertions(),
            GetAssignment => visitor.visit_get_assignment(),
            GetInfo { flag } => {
                let k = flag.accept(visitor)?;
                visitor.visit_get_info(k)
            }
            GetModel => visitor.visit_get_model(),
            GetOption { keyword } => {
                let k = keyword.accept(visitor)?;
                visitor.visit_get_option(k)
            }
            GetProof => visitor.visit_get_proof(),
            GetUnsatAssumptions => visitor.visit_get_unsat_assumptions(),
            GetUnsatCore => visitor.visit_get_unsat_core(),
            GetValue { terms } => {
                let ts = terms
                    .into_iter()
                    .map(|t| t.accept(visitor))
                    .collect::<Result<_, E>>()?;
                visitor.visit_get_value(ts)
            }
            Pop { level } => visitor.visit_pop(level),
            Push { level } => visitor.visit_push(level),
            Reset => visitor.visit_reset(),
            ResetAssertions => visitor.visit_reset_assertions(),
            SetInfo { keyword, value } => {
                let k = keyword.accept(visitor)?;
                let v = value.remap(
                    visitor,
                    |v, c: self::Constant| c.accept(v),
                    |v, s: Symbol| v.visit_bound_symbol(s.0),
                    |v, e: SExpr| e.accept(v),
                )?;
                visitor.visit_set_info(k, v)
            }
            SetLogic { symbol } => {
                let s = visitor.visit_bound_symbol(symbol.0)?;
                visitor.visit_set_logic(s)
            }
            SetOption { keyword, value } => {
                let k = keyword.accept(visitor)?;
                let v = value.remap(
                    visitor,
                    |v, c: self::Constant| c.accept(v),
                    |v, s: Symbol| v.visit_bound_symbol(s.0),
                    |v, e: SExpr| e.accept(v),
                )?;
                visitor.visit_set_option(k, v)
            }
        }
    }
}

impl Smt2Visitor for SyntaxBuilder {
    type Error = Error;
    type Constant = Constant;
    type QualIdentifier = QualIdentifier;
    type Keyword = Keyword;
    type Sort = Sort;
    type SExpr = SExpr;
    type Symbol = Symbol;
    type Term = Term;
    type Command = Command;

    fn syntax_error(&mut self, position: crate::smt2parser::Position, s: String) -> Self::Error {
        Error::SyntaxError(position, s)
    }

    fn parsing_error(&mut self, position: crate::smt2parser::Position, s: String) -> Self::Error {
        Error::ParsingError(position, s)
    }
}

impl std::fmt::Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨numeral⟩ | ⟨decimal⟩ | ⟨hexadecimal⟩ | ⟨binary⟩ | ⟨string⟩
        use Constant::*;
        match self {
            Numeral(num) => write!(f, "{}", num),
            Decimal(dec) => {
                let nom = dec.trunc();
                let mut denom = dec.fract();
                while !denom.is_integer() {
                    denom *= num::BigInt::from(10u32);
                }
                write!(f, "{}.{}", nom, denom)
            }
            Hexadecimal(hex) => {
                write!(f, "#x")?;
                for digit in hex {
                    write!(f, "{:x}", digit)?;
                }
                Ok(())
            }
            Binary(bin) => {
                write!(f, "#b")?;
                for digit in bin {
                    if *digit {
                        write!(f, "1")?;
                    } else {
                        write!(f, "0")?;
                    }
                }
                Ok(())
            }
            String(value) => {
                for s in value.split('"') {
                    write!(f, "\"{}\"", s)?;
                }
                Ok(())
            }
        }
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let c = self.0.as_bytes().first();
        if c.is_some()
            && lexer::is_non_digit_symbol_byte(*c.unwrap())
            && self.0.as_bytes().iter().all(|c| lexer::is_symbol_byte(*c))
        {
            write!(f, "{}", self.0)
        } else {
            write!(f, "|{}|", self.0)
        }
    }
}

impl std::fmt::Display for Keyword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, ":{}", self.0)
    }
}

impl<Constant, Symbol, Keyword> std::fmt::Display for SExpr<Constant, Symbol, Keyword>
where
    Constant: std::fmt::Display,
    Symbol: std::fmt::Display,
    Keyword: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨spec_constant⟩ | ⟨symbol⟩ | ⟨keyword⟩ | ( ⟨s_expr⟩∗ )
        use SExpr::*;
        match self {
            Constant(c) => write!(f, "{}", c),
            Symbol(s) => write!(f, "{}", s),
            Keyword(k) => write!(f, "{}", k),
            Application(values) => write!(f, "({})", values.iter().format(" ")),
        }
    }
}

impl<Identifier> std::fmt::Display for Sort<Identifier>
where
    Identifier: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨identifier⟩ | ( ⟨identifier⟩ ⟨sort⟩+ )
        use Sort::*;
        match self {
            Simple { identifier } => write!(f, "{}", identifier),
            Parameterized {
                identifier,
                parameters,
            } => write!(f, "({} {})", identifier, parameters.iter().format(" ")),
        }
    }
}

impl<Identifier> std::fmt::Display for QualIdentifier<Identifier>
where
    Identifier: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // ⟨identifier⟩ | ( as ⟨identifier⟩ ⟨sort⟩ )
        use QualIdentifier::*;
        match self {
            Simple { identifier } => write!(f, "{}", identifier),
            Sorted { identifier, sort } => write!(f, "(as {} {})", identifier, sort),
        }
    }
}

impl<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort> std::fmt::Display
    for Term<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort>
where
    Constant: std::fmt::Display,
    QualIdentifier: std::fmt::Display,
    Keyword: std::fmt::Display,
    SExpr: std::fmt::Display,
    Symbol: std::fmt::Display,
    Sort: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Term::*;
        match self {
            Constant(c) => {
                // ⟨spec_constant⟩
                write!(f, "{}", c)
            }
            QualIdentifier(id) => {
                // ⟨qual_identifier⟩
                write!(f, "{}", id)
            }
            Application {
                qual_identifier,
                arguments,
            } => {
                // ( ⟨qual_identifier ⟩ ⟨term⟩+ )
                write!(f, "({} {})", qual_identifier, arguments.iter().format(" "))
            }
            Let { var_bindings, term } => {
                // ( let ( ⟨var_binding⟩+ ) ⟨term⟩ )
                write!(
                    f,
                    "(let ({}) {})",
                    var_bindings
                        .iter()
                        .format_with(" ", |(v, t), f| f(&format_args!("({} {})", v, t))),
                    term
                )
            }
            Forall { vars, term } => {
                // ( forall ( ⟨sorted_var⟩+ ) ⟨term⟩ )
                write!(
                    f,
                    "(forall ({}) {})",
                    vars.iter()
                        .format_with(" ", |(v, s), f| f(&format_args!("({} {})", v, s))),
                    term
                )
            }
            Exists { vars, term } => {
                // ( exists ( ⟨sorted_var⟩+ ) ⟨term⟩ )
                write!(
                    f,
                    "(exists ({}) {})",
                    vars.iter()
                        .format_with(" ", |(v, s), f| f(&format_args!("({} {})", v, s))),
                    term
                )
            }
            Match { term, cases } => {
                // ( match ⟨term⟩ ( ⟨match_case⟩+ ) )
                write!(
                    f,
                    "(match {} ({}))",
                    term,
                    cases.iter().format_with(" ", |(pattern, term), f| {
                        if pattern.len() == 1 {
                            f(&format_args!("({} {})", &pattern[0], term))
                        } else {
                            f(&format_args!("(({}) {})", pattern.iter().format(" "), term))
                        }
                    })
                )
            }
            Attributes { term, attributes } => {
                // ( ! ⟨term⟩ ⟨attribute⟩+ )
                write!(
                    f,
                    "(! {} {})",
                    term,
                    attributes
                        .iter()
                        .format_with(" ", |(key, value), f| match value {
                            AttributeValue::None => f(key),
                            _ => f(&format_args!("{} {}", key, value)),
                        })
                )
            }
        }
    }
}

impl<Term, Symbol, Sort, Keyword, Constant, SExpr> std::fmt::Display
    for Command<Term, Symbol, Sort, Keyword, Constant, SExpr>
where
    Term: std::fmt::Display,
    Symbol: std::fmt::Display,
    Sort: std::fmt::Display,
    Keyword: std::fmt::Display,
    Constant: std::fmt::Display,
    SExpr: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Command::*;
        match self {
            Assert { term } => write!(f, "(assert {})", term),
            CheckSat => write!(f, "(check-sat)"),
            CheckSatAssuming { literals } => {
                // ( check-sat-assuming ( ⟨prop_literal⟩∗ ) )
                write!(
                    f,
                    "(check-sat-assuming ({}))",
                    literals.iter().format_with(" ", |(s, b), f| {
                        // ⟨symbol⟩ | ( not ⟨symbol⟩ )
                        if *b {
                            f(s)
                        } else {
                            f(&format_args!("(not {})", s))
                        }
                    })
                )
            }
            DeclareConst { symbol, sort } => write!(f, "(declare-const {} {})", symbol, sort),
            DeclareDatatype { symbol, datatype } => {
                write!(f, "(declare-datatype {} {})", symbol, datatype)
            }
            DeclareDatatypes { datatypes } => {
                // ( declare-datatypes ( ⟨sort_dec⟩n+1 ) ( ⟨datatype_dec⟩n+1 ) )
                let sorts = datatypes.iter().format_with(" ", |(sym, num, _), f| {
                    f(&format_args!("({} {})", sym, num))
                });
                let types = datatypes.iter().format_with(" ", |(_, _, ty), f| f(ty));
                write!(f, "(declare-datatypes ({}) ({}))", sorts, types)
            }
            DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                // ( declare-fun ⟨symbol⟩ ( ⟨sort⟩∗ ) ⟨sort⟩ )
                write!(
                    f,
                    "(declare-fun {} ({}) {})",
                    symbol,
                    parameters.iter().format(" "),
                    sort
                )
            }
            DeclareSort { symbol, arity } => write!(
                f,
                "(declare-sort {} {})",
                symbol,
                self::Constant::Numeral(arity.clone())
            ),
            DefineFun { sig, term } => {
                // ( define-fun ⟨function_dec⟩ ⟨term⟩ )
                write!(f, "(define-fun {} {})", sig, term)
            }
            DefineFunRec { sig, term } => {
                // ( define-fun-rec ⟨function_dec⟩ ⟨term⟩ )
                write!(f, "(define-fun {} {})", sig, term)
            }
            DefineFunsRec { funs } => {
                // ( define-funs-rec ( ( ⟨function_dec⟩ )n+1 ) ( ⟨term⟩n+1 ) )
                let sigs = funs.iter().format_with(" ", |(sig, _), f| f(sig));
                let terms = funs.iter().format_with(" ", |(_, t), f| f(t));
                write!(f, "(define-funs-rec ({}) ({}))", sigs, terms)
            }
            DefineSort {
                symbol,
                parameters,
                sort,
            } => {
                // ( define-sort ⟨symbol⟩ ( ⟨symbol⟩∗ ) ⟨sort⟩ )
                write!(
                    f,
                    "(define-sort {} ({}) {})",
                    symbol,
                    parameters.iter().format(" "),
                    sort
                )
            }
            Echo { message } => write!(f, "(echo {})", self::Constant::String(message.clone())),
            Exit => write!(f, "(exit)"),
            GetAssertions => write!(f, "(get-assertions)"),
            GetAssignment => write!(f, "(get-assignment)"),
            GetInfo { flag } => write!(f, "(get-info {})", flag),
            GetModel => write!(f, "(get-model)"),
            GetOption { keyword } => write!(f, "(get-info {})", keyword),
            GetProof => write!(f, "(get-proof)"),
            GetUnsatAssumptions => write!(f, "(get-unsat-assumptions)"),
            GetUnsatCore => write!(f, "(get-unsat-core)"),
            GetValue { terms } => {
                // ( get-value ( ⟨term⟩+ ) )
                write!(f, "(get-value ({}))", terms.iter().format(" "))
            }
            Pop { level } => write!(f, "(pop {})", self::Constant::Numeral(level.clone())),
            Push { level } => write!(f, "(push {})", self::Constant::Numeral(level.clone())),
            Reset => write!(f, "(reset)"),
            ResetAssertions => write!(f, "(reset-assertions)"),
            SetInfo { keyword, value } => write!(f, "(set-info {} {})", keyword, value),
            SetLogic { symbol } => write!(f, "(set-logic {})", symbol),
            SetOption { keyword, value } => write!(f, "(set-option {} {})", keyword, value),
        }
    }
}

/// Parse a single-token attribute value.
pub fn parse_simple_attribute_value(input: &str) -> Option<AttributeValue> {
    use crate::smt2parser::parser::Token;
    let token = lexer::Lexer::new(input.as_bytes()).next()?;
    match token {
        Token::Numeral(x) => Some(AttributeValue::Constant(Constant::Numeral(x))),
        Token::Decimal(x) => Some(AttributeValue::Constant(Constant::Decimal(x))),
        Token::String(x) => Some(AttributeValue::Constant(Constant::String(x))),
        Token::Binary(x) => Some(AttributeValue::Constant(Constant::Binary(x))),
        Token::Hexadecimal(x) => Some(AttributeValue::Constant(Constant::Hexadecimal(x))),
        Token::Symbol(x) => Some(AttributeValue::Symbol(Symbol(x))),
        _ => None,
    }
}

#[test]
fn test_syntax_visitor() {
    // (assert (let ((x (f x 2))) (= x 3)))
    let command = Command::Assert {
        term: Term::Let {
            var_bindings: vec![(
                Symbol("x".into()),
                Term::Application {
                    qual_identifier: QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("f".into()),
                        },
                    },
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("x".into()),
                            },
                        }),
                        Term::Constant(Constant::Numeral(num::BigUint::from(2u32))),
                    ],
                },
            )],
            term: Box::new(Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("=".into()),
                    },
                },
                arguments: vec![
                    Term::QualIdentifier(QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("x".into()),
                        },
                    }),
                    Term::Constant(Constant::Numeral(num::BigUint::from(3u32))),
                ],
            }),
        },
    };
    let mut builder = SyntaxBuilder;
    let command2 = command.clone().accept(&mut builder).unwrap();
    assert_eq!(command, command2);
}
