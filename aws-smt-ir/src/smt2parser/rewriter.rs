// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

// Modifications: Copyright (c) Amazon.com, Inc. or its affiliates. All Rights Reserved.

#![allow(clippy::type_complexity)]

//! Rewriting of Smt2 values

use crate::smt2parser::{
    visitors::{
        AttributeValue, CommandVisitor, ConstantVisitor, DatatypeDec, FunctionDec, Identifier,
        KeywordVisitor, QualIdentifierVisitor, SExprVisitor, Smt2Visitor, SortVisitor, SymbolKind,
        SymbolVisitor, TermVisitor,
    },
    Binary, Decimal, Hexadecimal, Numeral, Position,
};

/// Helper trait to create variants of an existing Smt2Visitor.
pub trait Rewriter {
    type V: Smt2Visitor;
    type Error: std::convert::From<<Self::V as Smt2Visitor>::Error>;

    /// Delegate visitor
    fn visitor(&mut self) -> &mut Self::V;

    // Post-processing
    fn process_constant(
        &mut self,
        value: <Self::V as Smt2Visitor>::Constant,
    ) -> Result<<Self::V as Smt2Visitor>::Constant, Self::Error> {
        Ok(value)
    }
    fn process_symbol(
        &mut self,
        value: <Self::V as Smt2Visitor>::Symbol,
    ) -> Result<<Self::V as Smt2Visitor>::Symbol, Self::Error> {
        Ok(value)
    }
    fn process_keyword(
        &mut self,
        value: <Self::V as Smt2Visitor>::Keyword,
    ) -> Result<<Self::V as Smt2Visitor>::Keyword, Self::Error> {
        Ok(value)
    }
    fn process_s_expr(
        &mut self,
        value: <Self::V as Smt2Visitor>::SExpr,
    ) -> Result<<Self::V as Smt2Visitor>::SExpr, Self::Error> {
        Ok(value)
    }
    fn process_sort(
        &mut self,
        value: <Self::V as Smt2Visitor>::Sort,
    ) -> Result<<Self::V as Smt2Visitor>::Sort, Self::Error> {
        Ok(value)
    }
    fn process_qual_identifier(
        &mut self,
        value: <Self::V as Smt2Visitor>::QualIdentifier,
    ) -> Result<<Self::V as Smt2Visitor>::QualIdentifier, Self::Error> {
        Ok(value)
    }
    fn process_term(
        &mut self,
        value: <Self::V as Smt2Visitor>::Term,
    ) -> Result<<Self::V as Smt2Visitor>::Term, Self::Error> {
        Ok(value)
    }
    fn process_command(
        &mut self,
        value: <Self::V as Smt2Visitor>::Command,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        Ok(value)
    }

    // ConstantVisitor
    fn visit_numeral_constant(
        &mut self,
        value: Numeral,
    ) -> Result<<Self::V as Smt2Visitor>::Constant, Self::Error> {
        let value = self.visitor().visit_numeral_constant(value)?;
        self.process_constant(value)
    }
    fn visit_decimal_constant(
        &mut self,
        value: Decimal,
    ) -> Result<<Self::V as Smt2Visitor>::Constant, Self::Error> {
        let value = self.visitor().visit_decimal_constant(value)?;
        self.process_constant(value)
    }
    fn visit_hexadecimal_constant(
        &mut self,
        value: Hexadecimal,
    ) -> Result<<Self::V as Smt2Visitor>::Constant, Self::Error> {
        let value = self.visitor().visit_hexadecimal_constant(value)?;
        self.process_constant(value)
    }
    fn visit_binary_constant(
        &mut self,
        value: Binary,
    ) -> Result<<Self::V as Smt2Visitor>::Constant, Self::Error> {
        let value = self.visitor().visit_binary_constant(value)?;
        self.process_constant(value)
    }
    fn visit_string_constant(
        &mut self,
        value: String,
    ) -> Result<<Self::V as Smt2Visitor>::Constant, Self::Error> {
        let value = self.visitor().visit_string_constant(value)?;
        self.process_constant(value)
    }

    // SymbolVisitor
    fn visit_bound_symbol(
        &mut self,
        value: String,
    ) -> Result<<Self::V as Smt2Visitor>::Symbol, Self::Error> {
        let value = self.visitor().visit_bound_symbol(value)?;
        self.process_symbol(value)
    }

    fn visit_fresh_symbol(
        &mut self,
        value: String,
        kind: SymbolKind,
    ) -> Result<<Self::V as Smt2Visitor>::Symbol, Self::Error> {
        let value = self.visitor().visit_fresh_symbol(value, kind)?;
        self.process_symbol(value)
    }

    fn visit_any_symbol(
        &mut self,
        value: String,
    ) -> Result<<Self::V as Smt2Visitor>::Symbol, Self::Error> {
        let value = self.visitor().visit_any_symbol(value)?;
        self.process_symbol(value)
    }

    fn bind_symbol(&mut self, symbol: &<Self::V as Smt2Visitor>::Symbol) {
        self.visitor().bind_symbol(symbol);
    }

    fn unbind_symbol(&mut self, symbol: &<Self::V as Smt2Visitor>::Symbol) {
        self.visitor().unbind_symbol(symbol);
    }

    // KeywordVisitor
    fn visit_keyword(
        &mut self,
        value: String,
    ) -> Result<<Self::V as Smt2Visitor>::Keyword, Self::Error> {
        let value = self.visitor().visit_keyword(value)?;
        self.process_keyword(value)
    }

    // SExprVisitor
    fn visit_constant_s_expr(
        &mut self,
        value: <Self::V as Smt2Visitor>::Constant,
    ) -> Result<<Self::V as Smt2Visitor>::SExpr, Self::Error> {
        let value = self.visitor().visit_constant_s_expr(value)?;
        self.process_s_expr(value)
    }
    fn visit_symbol_s_expr(
        &mut self,
        value: <Self::V as Smt2Visitor>::Symbol,
    ) -> Result<<Self::V as Smt2Visitor>::SExpr, Self::Error> {
        let value = self.visitor().visit_symbol_s_expr(value)?;
        self.process_s_expr(value)
    }
    fn visit_keyword_s_expr(
        &mut self,
        value: <Self::V as Smt2Visitor>::Keyword,
    ) -> Result<<Self::V as Smt2Visitor>::SExpr, Self::Error> {
        let value = self.visitor().visit_keyword_s_expr(value)?;
        self.process_s_expr(value)
    }
    fn visit_application_s_expr(
        &mut self,
        values: Vec<<Self::V as Smt2Visitor>::SExpr>,
    ) -> Result<<Self::V as Smt2Visitor>::SExpr, Self::Error> {
        let value = self.visitor().visit_application_s_expr(values)?;
        self.process_s_expr(value)
    }

    // SortVisitor
    fn visit_simple_sort(
        &mut self,
        identifier: Identifier<<Self::V as Smt2Visitor>::Symbol>,
    ) -> Result<<Self::V as Smt2Visitor>::Sort, Self::Error> {
        let value = self.visitor().visit_simple_sort(identifier)?;
        self.process_sort(value)
    }
    fn visit_parameterized_sort(
        &mut self,
        identifier: Identifier<<Self::V as Smt2Visitor>::Symbol>,
        parameters: Vec<<Self::V as Smt2Visitor>::Sort>,
    ) -> Result<<Self::V as Smt2Visitor>::Sort, Self::Error> {
        let value = self
            .visitor()
            .visit_parameterized_sort(identifier, parameters)?;
        self.process_sort(value)
    }

    // QualIdentifierVisitor
    fn visit_simple_identifier(
        &mut self,
        identifier: Identifier<<Self::V as Smt2Visitor>::Symbol>,
    ) -> Result<<Self::V as Smt2Visitor>::QualIdentifier, Self::Error> {
        let value = self.visitor().visit_simple_identifier(identifier)?;
        self.process_qual_identifier(value)
    }
    fn visit_sorted_identifier(
        &mut self,
        identifier: Identifier<<Self::V as Smt2Visitor>::Symbol>,
        sort: <Self::V as Smt2Visitor>::Sort,
    ) -> Result<<Self::V as Smt2Visitor>::QualIdentifier, Self::Error> {
        let value = self.visitor().visit_sorted_identifier(identifier, sort)?;
        self.process_qual_identifier(value)
    }

    // TermVisitor
    fn visit_constant(
        &mut self,
        constant: <Self::V as Smt2Visitor>::Constant,
    ) -> Result<<Self::V as Smt2Visitor>::Term, Self::Error> {
        let value = self.visitor().visit_constant(constant)?;
        self.process_term(value)
    }
    fn visit_qual_identifier(
        &mut self,
        qual_identifier: <Self::V as Smt2Visitor>::QualIdentifier,
    ) -> Result<<Self::V as Smt2Visitor>::Term, Self::Error> {
        let value = self.visitor().visit_qual_identifier(qual_identifier)?;
        self.process_term(value)
    }
    fn visit_application(
        &mut self,
        qual_identifier: <Self::V as Smt2Visitor>::QualIdentifier,
        arguments: Vec<<Self::V as Smt2Visitor>::Term>,
    ) -> Result<<Self::V as Smt2Visitor>::Term, Self::Error> {
        let value = self
            .visitor()
            .visit_application(qual_identifier, arguments)?;
        self.process_term(value)
    }
    fn visit_let(
        &mut self,
        var_bindings: Vec<(
            <Self::V as Smt2Visitor>::Symbol,
            <Self::V as Smt2Visitor>::Term,
        )>,
        term: <Self::V as Smt2Visitor>::Term,
    ) -> Result<<Self::V as Smt2Visitor>::Term, Self::Error> {
        let value = self.visitor().visit_let(var_bindings, term)?;
        self.process_term(value)
    }
    fn visit_forall(
        &mut self,
        vars: Vec<(
            <Self::V as Smt2Visitor>::Symbol,
            <Self::V as Smt2Visitor>::Sort,
        )>,
        term: <Self::V as Smt2Visitor>::Term,
    ) -> Result<<Self::V as Smt2Visitor>::Term, Self::Error> {
        let value = self.visitor().visit_forall(vars, term)?;
        self.process_term(value)
    }
    fn visit_exists(
        &mut self,
        vars: Vec<(
            <Self::V as Smt2Visitor>::Symbol,
            <Self::V as Smt2Visitor>::Sort,
        )>,
        term: <Self::V as Smt2Visitor>::Term,
    ) -> Result<<Self::V as Smt2Visitor>::Term, Self::Error> {
        let value = self.visitor().visit_exists(vars, term)?;
        self.process_term(value)
    }
    fn visit_match(
        &mut self,
        term: <Self::V as Smt2Visitor>::Term,
        cases: Vec<(
            Vec<<Self::V as Smt2Visitor>::Symbol>,
            <Self::V as Smt2Visitor>::Term,
        )>,
    ) -> Result<<Self::V as Smt2Visitor>::Term, Self::Error> {
        let value = self.visitor().visit_match(term, cases)?;
        self.process_term(value)
    }
    fn visit_attributes(
        &mut self,
        term: <Self::V as Smt2Visitor>::Term,
        attributes: Vec<(
            <Self::V as Smt2Visitor>::Keyword,
            AttributeValue<
                <Self::V as Smt2Visitor>::Constant,
                <Self::V as Smt2Visitor>::Symbol,
                <Self::V as Smt2Visitor>::SExpr,
            >,
        )>,
    ) -> Result<<Self::V as Smt2Visitor>::Term, Self::Error> {
        let value = self.visitor().visit_attributes(term, attributes)?;
        self.process_term(value)
    }

    // CommandVisitor
    fn visit_assert(
        &mut self,
        term: <Self::V as Smt2Visitor>::Term,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_assert(term)?;
        self.process_command(value)
    }
    fn visit_check_sat(&mut self) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_check_sat()?;
        self.process_command(value)
    }
    fn visit_check_sat_assuming(
        &mut self,
        literals: Vec<(<Self::V as Smt2Visitor>::Symbol, bool)>,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_check_sat_assuming(literals)?;
        self.process_command(value)
    }
    fn visit_declare_const(
        &mut self,
        symbol: <Self::V as Smt2Visitor>::Symbol,
        sort: <Self::V as Smt2Visitor>::Sort,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_declare_const(symbol, sort)?;
        self.process_command(value)
    }
    fn visit_declare_datatype(
        &mut self,
        symbol: <Self::V as Smt2Visitor>::Symbol,
        datatype: DatatypeDec<<Self::V as Smt2Visitor>::Symbol, <Self::V as Smt2Visitor>::Sort>,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_declare_datatype(symbol, datatype)?;
        self.process_command(value)
    }
    fn visit_declare_datatypes(
        &mut self,
        datatypes: Vec<(
            <Self::V as Smt2Visitor>::Symbol,
            Numeral,
            DatatypeDec<<Self::V as Smt2Visitor>::Symbol, <Self::V as Smt2Visitor>::Sort>,
        )>,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_declare_datatypes(datatypes)?;
        self.process_command(value)
    }
    fn visit_declare_fun(
        &mut self,
        symbol: <Self::V as Smt2Visitor>::Symbol,
        parameters: Vec<<Self::V as Smt2Visitor>::Sort>,
        sort: <Self::V as Smt2Visitor>::Sort,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_declare_fun(symbol, parameters, sort)?;
        self.process_command(value)
    }
    fn visit_declare_sort(
        &mut self,
        symbol: <Self::V as Smt2Visitor>::Symbol,
        arity: Numeral,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_declare_sort(symbol, arity)?;
        self.process_command(value)
    }
    fn visit_define_fun(
        &mut self,
        sig: FunctionDec<<Self::V as Smt2Visitor>::Symbol, <Self::V as Smt2Visitor>::Sort>,
        term: <Self::V as Smt2Visitor>::Term,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_define_fun(sig, term)?;
        self.process_command(value)
    }
    fn visit_define_fun_rec(
        &mut self,
        sig: FunctionDec<<Self::V as Smt2Visitor>::Symbol, <Self::V as Smt2Visitor>::Sort>,
        term: <Self::V as Smt2Visitor>::Term,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_define_fun_rec(sig, term)?;
        self.process_command(value)
    }
    fn visit_define_funs_rec(
        &mut self,
        funs: Vec<(
            FunctionDec<<Self::V as Smt2Visitor>::Symbol, <Self::V as Smt2Visitor>::Sort>,
            <Self::V as Smt2Visitor>::Term,
        )>,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_define_funs_rec(funs)?;
        self.process_command(value)
    }
    fn visit_define_sort(
        &mut self,
        symbol: <Self::V as Smt2Visitor>::Symbol,
        parameters: Vec<<Self::V as Smt2Visitor>::Symbol>,
        sort: <Self::V as Smt2Visitor>::Sort,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_define_sort(symbol, parameters, sort)?;
        self.process_command(value)
    }
    fn visit_echo(
        &mut self,
        message: String,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_echo(message)?;
        self.process_command(value)
    }
    fn visit_exit(&mut self) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_exit()?;
        self.process_command(value)
    }
    fn visit_get_assertions(&mut self) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_get_assertions()?;
        self.process_command(value)
    }
    fn visit_get_assignment(&mut self) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_get_assignment()?;
        self.process_command(value)
    }
    fn visit_get_info(
        &mut self,
        flag: <Self::V as Smt2Visitor>::Keyword,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_get_info(flag)?;
        self.process_command(value)
    }
    fn visit_get_model(&mut self) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_get_model()?;
        self.process_command(value)
    }
    fn visit_get_option(
        &mut self,
        keyword: <Self::V as Smt2Visitor>::Keyword,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_get_option(keyword)?;
        self.process_command(value)
    }
    fn visit_get_proof(&mut self) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_get_proof()?;
        self.process_command(value)
    }
    fn visit_get_unsat_assumptions(
        &mut self,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_get_unsat_assumptions()?;
        self.process_command(value)
    }
    fn visit_get_unsat_core(&mut self) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_get_unsat_core()?;
        self.process_command(value)
    }
    fn visit_get_value(
        &mut self,
        terms: Vec<<Self::V as Smt2Visitor>::Term>,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_get_value(terms)?;
        self.process_command(value)
    }
    fn visit_pop(
        &mut self,
        level: Numeral,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_pop(level)?;
        self.process_command(value)
    }
    fn visit_push(
        &mut self,
        level: Numeral,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_push(level)?;
        self.process_command(value)
    }
    fn visit_reset(&mut self) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_reset()?;
        self.process_command(value)
    }
    fn visit_reset_assertions(&mut self) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_reset_assertions()?;
        self.process_command(value)
    }
    fn visit_set_info(
        &mut self,
        keyword: <Self::V as Smt2Visitor>::Keyword,
        value: AttributeValue<
            <Self::V as Smt2Visitor>::Constant,
            <Self::V as Smt2Visitor>::Symbol,
            <Self::V as Smt2Visitor>::SExpr,
        >,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_set_info(keyword, value)?;
        self.process_command(value)
    }
    fn visit_set_logic(
        &mut self,
        symbol: <Self::V as Smt2Visitor>::Symbol,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_set_logic(symbol)?;
        self.process_command(value)
    }
    fn visit_set_option(
        &mut self,
        keyword: <Self::V as Smt2Visitor>::Keyword,
        value: AttributeValue<
            <Self::V as Smt2Visitor>::Constant,
            <Self::V as Smt2Visitor>::Symbol,
            <Self::V as Smt2Visitor>::SExpr,
        >,
    ) -> Result<<Self::V as Smt2Visitor>::Command, Self::Error> {
        let value = self.visitor().visit_set_option(keyword, value)?;
        self.process_command(value)
    }
}

impl<R, V> ConstantVisitor for R
where
    R: Rewriter<V = V>,
    V: Smt2Visitor,
{
    type T = V::Constant;
    type E = R::Error;

    fn visit_numeral_constant(&mut self, value: Numeral) -> Result<Self::T, Self::E> {
        self.visit_numeral_constant(value)
    }
    fn visit_decimal_constant(&mut self, value: Decimal) -> Result<Self::T, Self::E> {
        self.visit_decimal_constant(value)
    }
    fn visit_hexadecimal_constant(&mut self, value: Hexadecimal) -> Result<Self::T, Self::E> {
        self.visit_hexadecimal_constant(value)
    }
    fn visit_binary_constant(&mut self, value: Binary) -> Result<Self::T, Self::E> {
        self.visit_binary_constant(value)
    }
    fn visit_string_constant(&mut self, value: String) -> Result<Self::T, Self::E> {
        self.visit_string_constant(value)
    }
}

impl<R, V> SymbolVisitor for R
where
    R: Rewriter<V = V>,
    V: Smt2Visitor,
{
    type T = V::Symbol;
    type E = R::Error;

    fn visit_fresh_symbol(&mut self, value: String, kind: SymbolKind) -> Result<Self::T, Self::E> {
        self.visit_fresh_symbol(value, kind)
    }

    fn visit_bound_symbol(&mut self, value: String) -> Result<Self::T, Self::E> {
        self.visit_bound_symbol(value)
    }

    fn visit_any_symbol(&mut self, value: String) -> Result<Self::T, Self::E> {
        self.visit_any_symbol(value)
    }

    fn bind_symbol(&mut self, symbol: &Self::T) {
        self.bind_symbol(symbol)
    }

    fn unbind_symbol(&mut self, symbol: &Self::T) {
        self.unbind_symbol(symbol)
    }
}

impl<R, V> KeywordVisitor for R
where
    R: Rewriter<V = V>,
    V: Smt2Visitor,
{
    type T = V::Keyword;
    type E = R::Error;

    fn visit_keyword(&mut self, value: String) -> Result<Self::T, Self::E> {
        self.visit_keyword(value)
    }
}

impl<R, V> SExprVisitor<V::Constant, V::Symbol, V::Keyword> for R
where
    R: Rewriter<V = V>,
    V: Smt2Visitor,
{
    type T = V::SExpr;
    type E = R::Error;

    fn visit_constant_s_expr(&mut self, value: V::Constant) -> Result<Self::T, Self::E> {
        self.visit_constant_s_expr(value)
    }

    fn visit_symbol_s_expr(&mut self, value: V::Symbol) -> Result<Self::T, Self::E> {
        self.visit_symbol_s_expr(value)
    }

    fn visit_keyword_s_expr(&mut self, value: V::Keyword) -> Result<Self::T, Self::E> {
        self.visit_keyword_s_expr(value)
    }

    fn visit_application_s_expr(&mut self, values: Vec<Self::T>) -> Result<Self::T, Self::E> {
        self.visit_application_s_expr(values)
    }
}

impl<R, V> SortVisitor<V::Symbol> for R
where
    R: Rewriter<V = V>,
    V: Smt2Visitor,
{
    type T = V::Sort;
    type E = R::Error;

    fn visit_simple_sort(&mut self, identifier: Identifier<V::Symbol>) -> Result<Self::T, Self::E> {
        self.visit_simple_sort(identifier)
    }

    fn visit_parameterized_sort(
        &mut self,
        identifier: Identifier<V::Symbol>,
        parameters: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        self.visit_parameterized_sort(identifier, parameters)
    }
}

impl<R, V> QualIdentifierVisitor<Identifier<V::Symbol>, V::Sort> for R
where
    R: Rewriter<V = V>,
    V: Smt2Visitor,
{
    type T = V::QualIdentifier;
    type E = R::Error;

    fn visit_simple_identifier(
        &mut self,
        identifier: Identifier<V::Symbol>,
    ) -> Result<Self::T, Self::E> {
        self.visit_simple_identifier(identifier)
    }

    fn visit_sorted_identifier(
        &mut self,
        identifier: Identifier<V::Symbol>,
        sort: V::Sort,
    ) -> Result<Self::T, Self::E> {
        self.visit_sorted_identifier(identifier, sort)
    }
}

impl<R, V> TermVisitor<V::Constant, V::QualIdentifier, V::Keyword, V::SExpr, V::Symbol, V::Sort>
    for R
where
    R: Rewriter<V = V>,
    V: Smt2Visitor,
{
    type T = V::Term;
    type E = R::Error;

    fn visit_constant(&mut self, constant: V::Constant) -> Result<Self::T, Self::E> {
        self.visit_constant(constant)
    }

    fn visit_qual_identifier(
        &mut self,
        qual_identifier: V::QualIdentifier,
    ) -> Result<Self::T, Self::E> {
        self.visit_qual_identifier(qual_identifier)
    }

    fn visit_application(
        &mut self,
        qual_identifier: V::QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        self.visit_application(qual_identifier, arguments)
    }

    fn visit_let(
        &mut self,
        var_bindings: Vec<(V::Symbol, Self::T)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        self.visit_let(var_bindings, term)
    }

    fn visit_forall(
        &mut self,
        vars: Vec<(V::Symbol, V::Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        self.visit_forall(vars, term)
    }

    fn visit_exists(
        &mut self,
        vars: Vec<(V::Symbol, V::Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        self.visit_exists(vars, term)
    }

    fn visit_match(
        &mut self,
        term: Self::T,
        cases: Vec<(Vec<V::Symbol>, Self::T)>,
    ) -> Result<Self::T, Self::E> {
        self.visit_match(term, cases)
    }

    fn visit_attributes(
        &mut self,
        term: Self::T,
        attributes: Vec<(V::Keyword, AttributeValue<V::Constant, V::Symbol, V::SExpr>)>,
    ) -> Result<Self::T, Self::E> {
        self.visit_attributes(term, attributes)
    }
}

impl<R, V> CommandVisitor<V::Term, V::Symbol, V::Sort, V::Keyword, V::Constant, V::SExpr> for R
where
    R: Rewriter<V = V>,
    V: Smt2Visitor,
{
    type T = V::Command;
    type E = R::Error;

    fn visit_assert(&mut self, term: V::Term) -> Result<Self::T, Self::E> {
        self.visit_assert(term)
    }

    fn visit_check_sat(&mut self) -> Result<Self::T, Self::E> {
        self.visit_check_sat()
    }

    fn visit_check_sat_assuming(
        &mut self,
        literals: Vec<(V::Symbol, bool)>,
    ) -> Result<Self::T, Self::E> {
        self.visit_check_sat_assuming(literals)
    }

    fn visit_declare_const(
        &mut self,
        symbol: V::Symbol,
        sort: V::Sort,
    ) -> Result<Self::T, Self::E> {
        self.visit_declare_const(symbol, sort)
    }

    fn visit_declare_datatype(
        &mut self,
        symbol: V::Symbol,
        datatype: DatatypeDec<V::Symbol, V::Sort>,
    ) -> Result<Self::T, Self::E> {
        self.visit_declare_datatype(symbol, datatype)
    }

    fn visit_declare_datatypes(
        &mut self,
        datatypes: Vec<(V::Symbol, Numeral, DatatypeDec<V::Symbol, V::Sort>)>,
    ) -> Result<Self::T, Self::E> {
        self.visit_declare_datatypes(datatypes)
    }

    fn visit_declare_fun(
        &mut self,
        symbol: V::Symbol,
        parameters: Vec<V::Sort>,
        sort: V::Sort,
    ) -> Result<Self::T, Self::E> {
        self.visit_declare_fun(symbol, parameters, sort)
    }

    fn visit_declare_sort(
        &mut self,
        symbol: V::Symbol,
        arity: Numeral,
    ) -> Result<Self::T, Self::E> {
        self.visit_declare_sort(symbol, arity)
    }

    fn visit_define_fun(
        &mut self,
        sig: FunctionDec<V::Symbol, V::Sort>,
        term: V::Term,
    ) -> Result<Self::T, Self::E> {
        self.visit_define_fun(sig, term)
    }

    fn visit_define_fun_rec(
        &mut self,
        sig: FunctionDec<V::Symbol, V::Sort>,
        term: V::Term,
    ) -> Result<Self::T, Self::E> {
        self.visit_define_fun_rec(sig, term)
    }

    fn visit_define_funs_rec(
        &mut self,
        funs: Vec<(FunctionDec<V::Symbol, V::Sort>, V::Term)>,
    ) -> Result<Self::T, Self::E> {
        self.visit_define_funs_rec(funs)
    }

    fn visit_define_sort(
        &mut self,
        symbol: V::Symbol,
        parameters: Vec<V::Symbol>,
        sort: V::Sort,
    ) -> Result<Self::T, Self::E> {
        self.visit_define_sort(symbol, parameters, sort)
    }

    fn visit_echo(&mut self, message: String) -> Result<Self::T, Self::E> {
        self.visit_echo(message)
    }

    fn visit_exit(&mut self) -> Result<Self::T, Self::E> {
        self.visit_exit()
    }

    fn visit_get_assertions(&mut self) -> Result<Self::T, Self::E> {
        self.visit_get_assertions()
    }

    fn visit_get_assignment(&mut self) -> Result<Self::T, Self::E> {
        self.visit_get_assignment()
    }

    fn visit_get_info(&mut self, flag: V::Keyword) -> Result<Self::T, Self::E> {
        self.visit_get_info(flag)
    }

    fn visit_get_model(&mut self) -> Result<Self::T, Self::E> {
        self.visit_get_model()
    }

    fn visit_get_option(&mut self, keyword: V::Keyword) -> Result<Self::T, Self::E> {
        self.visit_get_option(keyword)
    }

    fn visit_get_proof(&mut self) -> Result<Self::T, Self::E> {
        self.visit_get_proof()
    }

    fn visit_get_unsat_assumptions(&mut self) -> Result<Self::T, Self::E> {
        self.visit_get_unsat_assumptions()
    }

    fn visit_get_unsat_core(&mut self) -> Result<Self::T, Self::E> {
        self.visit_get_unsat_core()
    }

    fn visit_get_value(&mut self, terms: Vec<V::Term>) -> Result<Self::T, Self::E> {
        self.visit_get_value(terms)
    }

    fn visit_pop(&mut self, level: Numeral) -> Result<Self::T, Self::E> {
        self.visit_pop(level)
    }

    fn visit_push(&mut self, level: Numeral) -> Result<Self::T, Self::E> {
        self.visit_push(level)
    }

    fn visit_reset(&mut self) -> Result<Self::T, Self::E> {
        self.visit_reset()
    }

    fn visit_reset_assertions(&mut self) -> Result<Self::T, Self::E> {
        self.visit_reset_assertions()
    }

    fn visit_set_info(
        &mut self,
        keyword: V::Keyword,
        value: AttributeValue<V::Constant, V::Symbol, V::SExpr>,
    ) -> Result<Self::T, Self::E> {
        self.visit_set_info(keyword, value)
    }

    fn visit_set_logic(&mut self, symbol: V::Symbol) -> Result<Self::T, Self::E> {
        self.visit_set_logic(symbol)
    }

    fn visit_set_option(
        &mut self,
        keyword: V::Keyword,
        value: AttributeValue<V::Constant, V::Symbol, V::SExpr>,
    ) -> Result<Self::T, Self::E> {
        self.visit_set_option(keyword, value)
    }
}

impl<R, V> Smt2Visitor for R
where
    R: Rewriter<V = V>,
    V: Smt2Visitor,
{
    type Error = R::Error;
    type Constant = V::Constant;
    type QualIdentifier = V::QualIdentifier;
    type Keyword = V::Keyword;
    type Sort = V::Sort;
    type SExpr = V::SExpr;
    type Symbol = V::Symbol;
    type Term = V::Term;
    type Command = V::Command;

    fn syntax_error(&mut self, pos: Position, s: String) -> Self::Error {
        self.visitor().syntax_error(pos, s).into()
    }

    fn parsing_error(&mut self, pos: Position, s: String) -> Self::Error {
        self.visitor().parsing_error(pos, s).into()
    }
}

#[test]
fn test_term_rewriter() {
    use crate::smt2parser::concrete::*;

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

    #[derive(Default)]
    struct Builder(crate::smt2parser::concrete::SyntaxBuilder);
    impl Rewriter for Builder {
        type V = crate::smt2parser::concrete::SyntaxBuilder;
        type Error = crate::smt2parser::concrete::Error;

        fn visitor(&mut self) -> &mut Self::V {
            &mut self.0
        }

        fn process_symbol(&mut self, s: Symbol) -> Result<Symbol, Self::Error> {
            Ok(Symbol(s.0 + "__"))
        }
    }

    let mut builder = Builder::default();

    let command2 = command.clone().accept(&mut builder).unwrap();
    let command3 = Command::Assert {
        term: Term::Let {
            var_bindings: vec![(
                Symbol("x__".into()),
                Term::Application {
                    qual_identifier: QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("f__".into()),
                        },
                    },
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("x__".into()),
                            },
                        }),
                        Term::Constant(Constant::Numeral(num::BigUint::from(2u32))),
                    ],
                },
            )],
            term: Box::new(Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("=__".into()),
                    },
                },
                arguments: vec![
                    Term::QualIdentifier(QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("x__".into()),
                        },
                    }),
                    Term::Constant(Constant::Numeral(num::BigUint::from(3u32))),
                ],
            }),
        },
    };

    assert_eq!(command2, command3);

    #[derive(Default)]
    struct Builder2(crate::smt2parser::concrete::SyntaxBuilder);
    impl Rewriter for Builder2 {
        type V = crate::smt2parser::concrete::SyntaxBuilder;
        type Error = crate::smt2parser::concrete::Error;

        fn visitor(&mut self) -> &mut Self::V {
            &mut self.0
        }

        fn visit_assert(&mut self, _: Term) -> Result<Command, Self::Error> {
            Ok(Command::Exit)
        }
    }

    let mut builder = Builder2::default();

    let command2 = command.accept(&mut builder).unwrap();
    let command3 = Command::Exit;
    assert_eq!(command2, command3);
}
