//! Implementations of conversion traits e.g. `From`, `TryFrom` for `Term` and related types.
//!
//! Currently, [`Term`] does not support SMT-LIB's `match` expression -- the
//! `TryFrom<crate::smt2parser::concrete::Term>` implementation for `Term` will return an error if it
//! encounters one.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    quantifier::{self, InvalidQuantifier, Quantifier},
    smt2parser::{concrete::Term as RawTerm, visitors::Index},
    term::operation::InvalidOp,
    uf::UninterpretedFunction,
    Command, Constant, IConst, ICoreOp, IIdentifier, IOp, ISort, ISymbol, IVar, Identifier, Let,
    Logic, Operation, ParseError, QualIdentifier, Sort, Symbol, Term, IUF,
};
use either::Either;
use std::{convert::TryFrom, marker::PhantomData};

pub fn convert_command<L: Logic>(
    command: crate::smt2parser::concrete::Command,
) -> Result<Command<Term<L>>, ParseError<L>>
where
    QualIdentifier: Into<L::Var>,
{
    command.accept(&mut Converter::default())
}

fn convert_qual_identifier(ident: crate::smt2parser::concrete::QualIdentifier) -> QualIdentifier {
    use crate::smt2parser::concrete::QualIdentifier::*;
    match ident {
        Simple { identifier } => QualIdentifier::Simple {
            identifier: convert_identifier(identifier).into(),
        },
        Sorted { identifier, sort } => QualIdentifier::Sorted {
            identifier: convert_identifier(identifier).into(),
            sort: ISort::from(Sort::from(sort)),
        },
    }
}

impl From<crate::smt2parser::concrete::Sort> for Sort {
    fn from(sort: crate::smt2parser::concrete::Sort) -> Self {
        use crate::smt2parser::concrete::Sort::*;
        match sort {
            Simple { identifier } => Self::Simple {
                identifier: convert_identifier(identifier).into(),
            },
            Parameterized {
                identifier,
                parameters,
            } => Self::Parameterized {
                identifier: convert_identifier(identifier).into(),
                parameters: parameters.into_iter().map(Into::into).collect(),
            },
        }
    }
}

impl From<crate::smt2parser::concrete::Sort> for ISort {
    fn from(sort: crate::smt2parser::concrete::Sort) -> Self {
        Sort::from(sort).into()
    }
}

fn convert_identifier(
    ident: crate::smt2parser::visitors::Identifier<Symbol>,
) -> Identifier<ISymbol> {
    use crate::smt2parser::visitors::Identifier::*;
    match ident {
        Simple { symbol } => Identifier::Simple {
            symbol: symbol.into(),
        },
        Indexed { symbol, indices } => Identifier::Indexed {
            symbol: symbol.into(),
            indices: indices
                .into_iter()
                .map(|index| match index {
                    Index::Numeral(x) => Index::Numeral(x),
                    Index::Symbol(s) => Index::Symbol(s.into()),
                })
                .collect(),
        },
    }
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum InvalidTerm<T: Logic> {
    #[error(transparent)]
    Op(#[from] InvalidOp<T>),
    #[error(transparent)]
    Quantifier(#[from] InvalidQuantifier<T>),
    #[error("SMT-LIB's `match` is currently unsupported")]
    Match,
}

fn convert<L: Logic>(t: RawTerm) -> Result<Term<L>, InvalidTerm<L>>
where
    QualIdentifier: Into<IVar<L::Var>>,
{
    #[derive(Debug)]
    enum Type {
        Op(QualIdentifier, usize),
        Let(Vec<ISymbol>),
        Quantifier(quantifier::Kind, Vec<(ISymbol, ISort)>),
    }

    let ident = convert_qual_identifier;

    let convert_or_enqueue = |t: RawTerm, pending: &mut Vec<_>| {
        use RawTerm::*;
        match t {
            Constant(c) => Ok(Some(Term::Constant(c.into()))),
            QualIdentifier(q) => {
                let t = (ICoreOp::parse(ident(q), vec![]).map(Term::CoreOp))
                    .or_else(|InvalidOp { func, .. }| IOp::parse(func, vec![]).map(Term::OtherOp))
                    .unwrap_or_else(|InvalidOp { func, .. }| Term::Variable(func.into()));
                Ok(Some(t))
            }
            Application {
                qual_identifier: op,
                arguments: args,
            } => {
                pending.push(Either::Left(Type::Op(ident(op), args.len())));
                pending.extend(args.into_iter().rev().map(Either::Right));
                Ok(None)
            }
            Let { var_bindings, term } => {
                let mut vars = vec![];
                let mut ts = vec![];
                for (var, t) in var_bindings {
                    vars.push(var.into());
                    ts.push(t);
                }
                pending.push(Either::Left(Type::Let(vars)));
                pending.extend(ts.into_iter().rev().map(Either::Right));
                pending.push(Either::Right(*term));
                Ok(None)
            }
            Forall { vars, term } => {
                let vars = vars
                    .into_iter()
                    .map(|(sym, sort)| (sym.into(), Sort::from(sort).into()))
                    .collect();
                pending.push(Either::Left(Type::Quantifier(
                    quantifier::Kind::Universal,
                    vars,
                )));
                pending.push(Either::Right(*term));
                Ok(None)
            }
            Exists { vars, term } => {
                let vars = vars
                    .into_iter()
                    .map(|(sym, sort)| (sym.into(), Sort::from(sort).into()))
                    .collect();
                pending.push(Either::Left(Type::Quantifier(
                    quantifier::Kind::Existential,
                    vars,
                )));
                pending.push(Either::Right(*term));
                Ok(None)
            }
            Match { .. } => Err(InvalidTerm::Match),
            Attributes { term, .. } => {
                pending.push(Either::Right(*term));
                Ok(None)
            }
        }
    };

    let mut pending = vec![];
    let mut converted: Vec<Term<L>> = vec![];

    if let Some(t) = convert_or_enqueue(t, &mut pending)? {
        return Ok(t);
    };

    while let Some(next) = pending.pop() {
        match next {
            Either::Left(ty) => match ty {
                Type::Op(func, num_args) => {
                    let args = converted.drain(converted.len() - num_args..);
                    let args = args.collect::<Vec<_>>();
                    let op = (ICoreOp::parse(func, args).map(Term::CoreOp))
                        .or_else(|InvalidOp { func, args }| IOp::parse(func, args).map(Into::into))
                        .or_else(|InvalidOp { func, args }| {
                            IUF::parse(func.sym().clone(), args).map(Into::into)
                        })?;
                    converted.push(op);
                }
                Type::Let(vars) => {
                    let ts = converted.drain(converted.len() - vars.len()..);
                    let bindings = vars.into_iter().zip(ts).collect();
                    let term = converted.pop().unwrap();
                    converted.push(Term::Let(Let { bindings, term }.into()));
                }
                Type::Quantifier(kind, vars) => {
                    let t = converted.pop().unwrap();
                    let q = L::Quantifier::parse(kind, vars, t)?.into();
                    converted.push(Term::Quantifier(q));
                }
            },
            Either::Right(t) => {
                if let Some(t) = convert_or_enqueue(t, &mut pending)? {
                    converted.push(t);
                }
            }
        }
    }

    Ok(converted.pop().unwrap())
}

#[test]
fn basic() {
    let smt = "(assert (and (or (not x) (not y)) (and x (not y))))";
    let cmd = crate::parse_commands(smt.as_bytes()).next().unwrap();
    match cmd.unwrap() {
        crate::smt2parser::concrete::Command::Assert { term } => {
            let var = |x| Term::from(IVar::from(QualIdentifier::from(x)));
            let (x, y) = (var("x"), var("y"));
            assert_eq!(
                convert::<crate::logic::ALL>(term).unwrap(),
                (!x.clone() | !y.clone()) & (x & !y)
            );
        }
        _ => panic!("parsed as wrong command type"),
    }
}

#[derive(Default)]
pub(crate) struct Converter<L>(PhantomData<L>);

impl<T: Logic> TryFrom<RawTerm> for Term<T>
where
    QualIdentifier: Into<IVar<T::Var>>,
{
    type Error = InvalidTerm<T>;

    fn try_from(term: RawTerm) -> Result<Self, Self::Error> {
        convert(term)
    }
}

impl<T: Logic> From<IConst> for Term<T> {
    fn from(c: IConst) -> Self {
        Self::Constant(c)
    }
}

impl<T: Logic> From<Constant> for Term<T> {
    fn from(c: Constant) -> Self {
        Self::Constant(c.into())
    }
}

impl<T: Logic<Var = QualIdentifier>> From<ISymbol> for Term<T> {
    fn from(sym: ISymbol) -> Self {
        Term::Variable(sym.into())
    }
}

impl<T: Logic> From<IVar<T::Var>> for Term<T> {
    fn from(v: IVar<T::Var>) -> Self {
        Self::Variable(v)
    }
}

impl<T: Logic> From<&IVar<T::Var>> for Term<T> {
    fn from(v: &IVar<T::Var>) -> Self {
        Self::Variable(v.clone())
    }
}

mod visitors {
    use super::*;
    use crate::smt2parser::{
        concrete::{Keyword, SyntaxBuilder},
        visitors::*,
        Numeral,
    };
    use crate::{
        AttributeValue, Command, DatatypeDec, FunctionDec, IQuantifier, ParseError, SExpr,
    };

    impl<L: Logic> TermVisitor<IConst, QualIdentifier, Keyword, SExpr, ISymbol, ISort> for Converter<L>
    where
        QualIdentifier: Into<L::Var>,
    {
        type T = Term<L>;
        type E = ParseError<L>;

        fn visit_constant(&mut self, constant: IConst) -> Result<Self::T, Self::E> {
            Ok(constant.into())
        }

        fn visit_qual_identifier(&mut self, func: QualIdentifier) -> Result<Self::T, Self::E> {
            Ok((ICoreOp::parse(func, vec![]).map(Term::CoreOp))
                .or_else(|InvalidOp { func, .. }| IOp::parse(func, vec![]).map(Term::OtherOp))
                .unwrap_or_else(|InvalidOp { func, .. }| Term::Variable(IVar::from(func.into()))))
        }

        fn visit_application(
            &mut self,
            func: QualIdentifier,
            args: Vec<Self::T>,
        ) -> Result<Self::T, Self::E> {
            (ICoreOp::parse(func, args).map(Term::CoreOp))
                .or_else(|InvalidOp { func, args }| IOp::parse(func, args).map(Into::into))
                .or_else(|InvalidOp { func, args }| {
                    IUF::parse(func.sym().clone(), args).map(Into::into)
                })
                .map_err(Into::into)
        }

        fn visit_let(
            &mut self,
            bindings: Vec<(ISymbol, Self::T)>,
            term: Self::T,
        ) -> Result<Self::T, Self::E> {
            Ok(Let { bindings, term }.into())
        }

        fn visit_forall(
            &mut self,
            vars: Vec<(ISymbol, ISort)>,
            term: Self::T,
        ) -> Result<Self::T, Self::E> {
            Quantifier::parse(quantifier::Kind::Universal, vars, term)
                .map(|q| Term::from(IQuantifier::new(q)))
                .map_err(Into::into)
        }

        fn visit_exists(
            &mut self,
            vars: Vec<(ISymbol, ISort)>,
            term: Self::T,
        ) -> Result<Self::T, Self::E> {
            Quantifier::parse(quantifier::Kind::Existential, vars, term)
                .map(|q| Term::from(IQuantifier::new(q)))
                .map_err(Into::into)
        }

        fn visit_match(
            &mut self,
            _term: Self::T,
            _cases: Vec<(Vec<ISymbol>, Self::T)>,
        ) -> Result<Self::T, Self::E> {
            unimplemented!("match is currently unsupported")
        }

        fn visit_attributes(
            &mut self,
            term: Self::T,
            _attributes: Vec<(Keyword, AttributeValue)>,
        ) -> Result<Self::T, Self::E> {
            // TODO: take attributes into account?
            eprintln!("warning: attributes are currently ignored");
            Ok(term)
        }
    }

    impl<L: Logic> SortVisitor<ISymbol> for Converter<L> {
        type T = ISort;
        type E = ParseError<L>;

        fn visit_simple_sort(
            &mut self,
            identifier: Identifier<ISymbol>,
        ) -> Result<Self::T, Self::E> {
            let identifier = identifier.into();
            Ok(Sort::Simple { identifier }.into())
        }

        fn visit_parameterized_sort(
            &mut self,
            identifier: Identifier<ISymbol>,
            parameters: Vec<Self::T>,
        ) -> Result<Self::T, Self::E> {
            let identifier = identifier.into();
            Ok(Sort::Parameterized {
                identifier,
                parameters,
            }
            .into())
        }
    }

    impl<L: Logic> SymbolVisitor for Converter<L> {
        type T = ISymbol;
        type E = ParseError<L>;

        fn visit_fresh_symbol(
            &mut self,
            value: String,
            _kind: SymbolKind,
        ) -> Result<Self::T, Self::E> {
            Ok(Symbol(value).into())
        }
    }

    impl<L: Logic> QualIdentifierVisitor<Identifier<ISymbol>, ISort> for Converter<L> {
        type T = QualIdentifier;
        type E = ParseError<L>;

        fn visit_simple_identifier(
            &mut self,
            identifier: Identifier<ISymbol>,
        ) -> Result<Self::T, Self::E> {
            Ok(QualIdentifier::Simple {
                identifier: IIdentifier::new(identifier),
            })
        }

        fn visit_sorted_identifier(
            &mut self,
            identifier: Identifier<ISymbol>,
            sort: ISort,
        ) -> Result<Self::T, Self::E> {
            Ok(QualIdentifier::Sorted {
                identifier: IIdentifier::new(identifier),
                sort,
            })
        }
    }

    impl<L: Logic> ConstantVisitor for Converter<L> {
        type T = IConst;
        type E = ParseError<L>;

        fn visit_numeral_constant(
            &mut self,
            value: crate::smt2parser::Numeral,
        ) -> Result<Self::T, Self::E> {
            Ok(crate::types::Constant::Numeral(value).into())
        }

        fn visit_decimal_constant(
            &mut self,
            value: crate::smt2parser::Decimal,
        ) -> Result<Self::T, Self::E> {
            Ok(crate::types::Constant::Decimal(value).into())
        }

        fn visit_hexadecimal_constant(
            &mut self,
            value: crate::smt2parser::Hexadecimal,
        ) -> Result<Self::T, Self::E> {
            Ok(crate::types::Constant::Hexadecimal(value).into())
        }

        fn visit_binary_constant(
            &mut self,
            value: crate::smt2parser::Binary,
        ) -> Result<Self::T, Self::E> {
            Ok(crate::types::Constant::Binary(value).into())
        }

        fn visit_string_constant(&mut self, value: String) -> Result<Self::T, Self::E> {
            Ok(crate::types::Constant::String(value).into())
        }
    }

    impl<L: Logic> KeywordVisitor for Converter<L> {
        type T = Keyword;
        type E = ParseError<L>;

        fn visit_keyword(&mut self, value: String) -> Result<Self::T, Self::E> {
            Ok(Keyword(value))
        }
    }

    impl<L: Logic> SExprVisitor<IConst, ISymbol, Keyword> for Converter<L> {
        type T = SExpr;
        type E = ParseError<L>;

        fn visit_constant_s_expr(&mut self, value: IConst) -> Result<Self::T, Self::E> {
            Ok(SExpr::Constant(value))
        }

        fn visit_symbol_s_expr(&mut self, value: ISymbol) -> Result<Self::T, Self::E> {
            Ok(SExpr::Symbol(value))
        }

        fn visit_keyword_s_expr(&mut self, value: Keyword) -> Result<Self::T, Self::E> {
            Ok(SExpr::Keyword(value))
        }

        fn visit_application_s_expr(&mut self, values: Vec<Self::T>) -> Result<Self::T, Self::E> {
            Ok(SExpr::Application(values))
        }
    }

    impl<L: Logic> CommandVisitor<Term<L>, ISymbol, ISort, Keyword, IConst, SExpr> for Converter<L> {
        type T = Command<Term<L>>;
        type E = ParseError<L>;

        fn visit_assert(&mut self, term: Term<L>) -> Result<Self::T, Self::E> {
            Ok(Command::Assert { term })
        }

        fn visit_check_sat(&mut self) -> Result<Self::T, Self::E> {
            Ok(Command::CheckSat)
        }

        fn visit_check_sat_assuming(
            &mut self,
            literals: Vec<(ISymbol, bool)>,
        ) -> Result<Self::T, Self::E> {
            Ok(Command::CheckSatAssuming { literals })
        }

        fn visit_declare_const(
            &mut self,
            symbol: ISymbol,
            sort: ISort,
        ) -> Result<Self::T, Self::E> {
            Ok(Command::DeclareConst { symbol, sort })
        }

        fn visit_declare_datatype(
            &mut self,
            symbol: ISymbol,
            datatype: DatatypeDec,
        ) -> Result<Self::T, Self::E> {
            Ok(Command::DeclareDatatype { symbol, datatype })
        }

        fn visit_declare_datatypes(
            &mut self,
            datatypes: Vec<(ISymbol, Numeral, DatatypeDec)>,
        ) -> Result<Self::T, Self::E> {
            Ok(Command::DeclareDatatypes { datatypes })
        }

        fn visit_declare_fun(
            &mut self,
            symbol: ISymbol,
            parameters: Vec<ISort>,
            sort: ISort,
        ) -> Result<Self::T, Self::E> {
            Ok(Command::DeclareFun {
                symbol,
                parameters,
                sort,
            })
        }

        fn visit_declare_sort(
            &mut self,
            symbol: ISymbol,
            arity: Numeral,
        ) -> Result<Self::T, Self::E> {
            Ok(Command::DeclareSort { symbol, arity })
        }

        fn visit_define_fun(
            &mut self,
            sig: FunctionDec,
            term: Term<L>,
        ) -> Result<Self::T, Self::E> {
            Ok(Command::DefineFun { sig, term })
        }

        fn visit_define_fun_rec(
            &mut self,
            sig: FunctionDec,
            term: Term<L>,
        ) -> Result<Self::T, Self::E> {
            Ok(Command::DefineFunRec { sig, term })
        }

        fn visit_define_funs_rec(
            &mut self,
            funs: Vec<(FunctionDec, Term<L>)>,
        ) -> Result<Self::T, Self::E> {
            Ok(Command::DefineFunsRec { funs })
        }

        fn visit_define_sort(
            &mut self,
            symbol: ISymbol,
            parameters: Vec<ISymbol>,
            sort: ISort,
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

        fn visit_get_value(&mut self, terms: Vec<Term<L>>) -> Result<Self::T, Self::E> {
            Ok(Command::GetValue { terms })
        }

        fn visit_pop(&mut self, level: Numeral) -> Result<Self::T, Self::E> {
            Ok(Command::Pop { level })
        }

        fn visit_push(&mut self, level: crate::smt2parser::Numeral) -> Result<Self::T, Self::E> {
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
            value: AttributeValue,
        ) -> Result<Self::T, Self::E> {
            Ok(Command::SetInfo { keyword, value })
        }

        fn visit_set_logic(&mut self, symbol: ISymbol) -> Result<Self::T, Self::E> {
            Ok(Command::SetLogic { symbol })
        }

        fn visit_set_option(
            &mut self,
            keyword: Keyword,
            value: AttributeValue,
        ) -> Result<Self::T, Self::E> {
            Ok(Command::SetOption { keyword, value })
        }
    }

    impl<L: Logic> Smt2Visitor for Converter<L>
    where
        QualIdentifier: Into<L::Var>,
    {
        type Error = ParseError<L>;
        type Constant = IConst;
        type QualIdentifier = QualIdentifier;
        type Keyword = Keyword;
        type Sort = ISort;
        type SExpr = SExpr;
        type Symbol = ISymbol;
        type Term = Term<L>;
        type Command = Command<Term<L>>;

        fn syntax_error(
            &mut self,
            position: crate::smt2parser::Position,
            s: String,
        ) -> Self::Error {
            <SyntaxBuilder as Smt2Visitor>::syntax_error(&mut SyntaxBuilder, position, s).into()
        }

        fn parsing_error(
            &mut self,
            position: crate::smt2parser::Position,
            s: String,
        ) -> Self::Error {
            <SyntaxBuilder as Smt2Visitor>::parsing_error(&mut SyntaxBuilder, position, s).into()
        }
    }
}
