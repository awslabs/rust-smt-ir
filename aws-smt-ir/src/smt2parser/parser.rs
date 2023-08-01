// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

// Modifications: Copyright (c) Amazon.com, Inc. or its affiliates. All Rights Reserved.

#![allow(unused_braces)]
#![allow(clippy::type_complexity)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::needless_lifetimes)]
#![allow(clippy::let_unit_value)]

pub use internal::{Parser, Token};

pomelo! {
    %module internal;
    %include { use crate::smt2parser::visitors; }

    %stack_size 0;

    %parser pub struct Parser<'a, T: visitors::Smt2Visitor> {};
    %extra_argument (&'a mut T, &'a mut crate::smt2parser::lexer::Position);
    %error T::Error;
    %syntax_error { match token {
        Some(token) => Err(extra.0.syntax_error(extra.1.clone(), format!("unexpected token: {:?}", token))),
        None => Err(extra.0.syntax_error(extra.1.clone(), "unexpected end of input".into())),
    }};
    %parse_fail { extra.0.parsing_error(extra.1.clone(), "unrecoverable parsing error".into()) };
    %token #[derive(Clone, Debug, PartialEq, Eq)] pub enum Token {};

    %type Keyword String;
    %type Symbol String;
    %type Numeral crate::smt2parser::Numeral;
    %type Decimal crate::smt2parser::Decimal;
    %type Hexadecimal crate::smt2parser::Hexadecimal;
    %type Binary crate::smt2parser::Binary;
    %type String String;

    // Amazon update: All reserved word tokens are strings equal to the reserved word (see lexer.rs)
    %type Underscore String;
    %type Exclam String;
    %type As String;
    %type Let String;
    %type Exists String;
    %type Forall String;
    %type Match String;
    %type Par String;
    %type Assert String;
    %type CheckSat String;
    %type CheckSatAssuming String;
    %type DeclareConst String;
    %type DeclareDatatype String;
    %type DeclareDatatypes String;
    %type DeclareFun String;
    %type DeclareSort String;
    %type DefineFun String;
    %type DefineFunRec String;
    %type DefineFunsRec String;
    %type DefineSort String;
    %type Echo String;
    %type Exit String;
    %type GetAssertions String;
    %type GetAssignment String;
    %type GetInfo String;
    %type GetModel String;
    %type GetOption String;
    %type GetProof String;
    %type GetUnsatAssumptions String;
    %type GetUnsatCore String;
    %type GetValue String;
    %type Pop String;
    %type Push String;
    %type Reset String;
    %type ResetAssertions String;
    %type SetInfo String;
    %type SetLogic String;
    %type SetOption String;

    %type reserved T::Symbol;
    // end of Amazon update

    %type command T::Command;

    %type term T::Term;
    %type terms Vec<T::Term>;

    %type constant T::Constant;
    %type qual_identifier T::QualIdentifier;
    %type identifier visitors::Identifier<T::Symbol>;

    %type bound_symbol T::Symbol;
    %type fresh_symbol T::Symbol;
    %type fresh_symbols Vec<T::Symbol>;
    %type any_symbol T::Symbol;
    %type pattern_symbols Vec<T::Symbol>;
    %type pattern Vec<T::Symbol>;

    %type keyword T::Keyword;

    %type sort T::Sort;
    %type sorts Vec<T::Sort>;

    %type attribute_value visitors::AttributeValue<T::Constant, T::Symbol, T::SExpr>;
    %type attributes Vec<(T::Keyword, visitors::AttributeValue<T::Constant, T::Symbol, T::SExpr>)>;

    %type s_expr T::SExpr;
    %type s_exprs Vec<T::SExpr>;

    %type index visitors::Index<T::Symbol>;
    %type indices Vec<visitors::Index<T::Symbol>>;

    %type var_binding (T::Symbol, T::Term);
    %type var_bindings Vec<(T::Symbol, T::Term)>;

    %type sorted_var (T::Symbol, T::Sort);
    %type sorted_vars Vec<(T::Symbol, T::Sort)>;

    %type match_case (Vec<T::Symbol>, T::Term);
    %type match_cases Vec<(Vec<T::Symbol>, T::Term)>;

    %type prop_literal (T::Symbol, bool);
    %type prop_literals Vec<(T::Symbol, bool)>;

    %type datatype_dec visitors::DatatypeDec<T::Symbol, T::Sort>;
    %type datatype_decs Vec<visitors::DatatypeDec<T::Symbol, T::Sort>>;

    %type selector_dec (T::Symbol, T::Sort);
    %type selector_decs Vec<(T::Symbol, T::Sort)>;

    %type constructor_dec visitors::ConstructorDec<T::Symbol, T::Sort>;
    %type constructor_decs Vec<visitors::ConstructorDec<T::Symbol, T::Sort>>;

    %type function_dec visitors::FunctionDec<T::Symbol, T::Sort>;
    %type function_decs Vec<visitors::FunctionDec<T::Symbol, T::Sort>>;

    %type sort_dec (T::Symbol, crate::smt2parser::Numeral);
    %type sort_decs Vec<(T::Symbol, crate::smt2parser::Numeral)>;

    %start_symbol command;

    bound_symbol ::= Symbol(s) { extra.0.visit_bound_symbol(s)? }
    fresh_symbol ::= Symbol(s) { extra.0.visit_fresh_symbol(s, crate::smt2parser::visitors::SymbolKind::Unknown)? }
    any_symbol ::= Symbol(s) { extra.0.visit_any_symbol(s)? }
    keyword ::= Keyword(s) { extra.0.visit_keyword(s)? }

    fresh_symbols ::= fresh_symbol(x) { vec![x] }
    fresh_symbols ::= fresh_symbols(mut xs) fresh_symbol(x) { xs.push(x); xs }
    pattern_symbols ::= any_symbol(x) { vec![x] }
    pattern_symbols ::= fresh_symbols(mut xs) fresh_symbol(x) { xs.push(x); xs }

    // attribute_value ::= ⟨spec_constant⟩ | ⟨symbol⟩ | ( ⟨s_expr⟩∗ ) |
    attribute_value ::= constant(x) { visitors::AttributeValue::Constant(x) }
    attribute_value ::= bound_symbol(x) { visitors::AttributeValue::Symbol(x) }
    attribute_value ::= LeftParen s_exprs?(xs) RightParen { visitors::AttributeValue::SExpr(xs.unwrap_or_default()) }
    attribute_value ::= { visitors::AttributeValue::None }

    attributes ::= keyword(k) attribute_value(v) { vec![(k, v)] }
    attributes ::= attributes(mut xs) keyword(k) attribute_value(v) { xs.push((k, v)); xs }

    // Amazon addition: in an s_expr the tokens `let`, `forall`, etc. must be converted to symbols
    reserved ::= Underscore | Exclam | As | Let | Exists | Forall | Match | Par |
                 Assert | CheckSat | CheckSatAssuming | DeclareConst | DeclareDatatype |
                 DeclareDatatypes | DeclareFun | DeclareSort | DefineFun | DefineFunRec |
                 DefineFunsRec | DefineSort | Echo | Exit | GetAssertions | GetAssignment |
                 GetInfo | GetModel | GetOption | GetProof | GetUnsatAssumptions | GetUnsatCore |
                 GetValue | Pop | Push | Reset | ResetAssertions | SetInfo | SetLogic |
                 SetOption (t) { extra.0.visit_any_symbol(t)? }

    s_expr ::= reserved(x) { extra.0.visit_symbol_s_expr(x)? }
    // end of Amazon additions

    // s_expr ::= ⟨spec_constant⟩ | ⟨symbol⟩ | ⟨keyword⟩ | ( ⟨s_expr⟩∗ )
    s_expr ::= constant(x) { extra.0.visit_constant_s_expr(x)? }
    s_expr ::= bound_symbol(x) { extra.0.visit_symbol_s_expr(x)? }
    s_expr ::= keyword(x) { extra.0.visit_keyword_s_expr(x)? }
    s_expr ::= LeftParen s_exprs?(xs) RightParen { extra.0.visit_application_s_expr(xs.unwrap_or_default())? }

    s_exprs ::= s_expr(x) { vec![x] }
    s_exprs ::= s_exprs(mut xs) s_expr(x) { xs.push(x); xs }

    // index ::= ⟨numeral⟩ | ⟨symbol⟩
    index ::= Numeral(x) { visitors::Index::Numeral(x) }
    index ::= bound_symbol(x) { visitors::Index::Symbol(x) }

    indices ::= index(x) { vec![x] }
    indices ::= indices(mut xs) index(x) { xs.push(x); xs }

    // identifier ::= ⟨symbol⟩ | ( _ ⟨symbol⟩ ⟨index⟩+ )
    identifier ::= bound_symbol(symbol) { visitors::Identifier::Simple { symbol } }
    identifier ::= LeftParen Underscore bound_symbol(symbol) indices(indices) RightParen { visitors::Identifier::Indexed { symbol, indices } }

    // sort ::= ⟨identifier⟩ | ( ⟨identifier⟩ ⟨sort⟩+ )
    sort ::= identifier(id) { extra.0.visit_simple_sort(id)? }
    sort ::= LeftParen identifier(id) sorts(sorts) RightParen { extra.0.visit_parameterized_sort(id, sorts)? }

    sorts ::= sort(x) { vec![x] }
    sorts ::= sorts(mut xs) sort(x) { xs.push(x); xs }

    // qual_identifier ::= ⟨identifier⟩ | ( as ⟨identifier⟩ ⟨sort⟩ )
    qual_identifier ::= identifier(x) { extra.0.visit_simple_identifier(x)? }
    qual_identifier ::= LeftParen As identifier(id) sort(s) RightParen { extra.0.visit_sorted_identifier(id, s)? }

    // constant ::= ⟨numeral⟩ | ⟨decimal⟩ | ⟨hexadecimal⟩ | ⟨binary⟩ | ⟨string⟩
    constant ::= Numeral(x) { extra.0.visit_numeral_constant(x)? }
    constant ::= Decimal(x) { extra.0.visit_decimal_constant(x)? }
    constant ::= Hexadecimal(x) { extra.0.visit_hexadecimal_constant(x)? }
    constant ::= Binary(x) { extra.0.visit_binary_constant(x)? }
    constant ::= String(x) { extra.0.visit_string_constant(x)? }

    // ⟨var_binding⟩ ::= ( ⟨symbol⟩ ⟨term⟩ )
    var_binding ::= LeftParen fresh_symbol(s) term(t) RightParen { (s, t) }

    var_bindings ::= var_binding(x) { vec![x] }
    var_bindings ::= var_bindings(mut xs) var_binding(x) { xs.push(x); xs }

    // ⟨sorted_var⟩ ::= ( ⟨symbol⟩ ⟨sort⟩ )
    sorted_var ::= LeftParen fresh_symbol(s) sort(x) RightParen { (s, x) }

    sorted_vars ::= sorted_var(x) { vec![x] }
    sorted_vars ::= sorted_vars(mut xs) sorted_var(x) { xs.push(x); xs }

    // pattern ::= ⟨symbol⟩ | ( ⟨symbol⟩ ⟨symbol⟩+ )
    pattern ::= any_symbol(x) { vec![x] }
    pattern ::= LeftParen pattern_symbols(xs) RightParen { xs }

    // ⟨match_case⟩ ::= ( ⟨pattern⟩ ⟨term⟩ )
    match_case ::= LeftParen pattern(p) term(t) RightParen { (p, t) }

    match_cases ::= match_case(x) { vec![x] }
    match_cases ::= match_cases(mut xs) match_case(x) { xs.push(x); xs }

    // terms ::= ...
    //   ⟨spec_constant⟩
    term ::= constant(x) { extra.0.visit_constant(x)? }
    //   ⟨qual_identifier⟩
    term ::= qual_identifier(x) { extra.0.visit_qual_identifier(x)? }
    //   ( let ( ⟨var_binding⟩+ ) ⟨term⟩ )
    term ::= LeftParen Let LeftParen var_bindings(xs) RightParen term(t) RightParen { extra.0.visit_let(xs, t)? }
    //   ( forall ( ⟨sorted_var⟩+ ) ⟨term⟩ )
    term ::= LeftParen Forall LeftParen sorted_vars(xs) RightParen term(t) RightParen { extra.0.visit_forall(xs, t)? }
    //   ( exists ( ⟨sorted_var⟩+ ) ⟨term⟩ )
    term ::= LeftParen Exists LeftParen sorted_vars(xs) RightParen term(t) RightParen { extra.0.visit_exists(xs, t)? }
    //   ( match ⟨term⟩ ( ⟨match_case⟩+ ) )
    term ::= LeftParen Match term(t) LeftParen match_cases(xs) RightParen RightParen { extra.0.visit_match(t, xs)? }
    //   ( ! ⟨term⟩ ⟨attribute⟩+ )
    term ::= LeftParen Exclam term(t) attributes(xs) RightParen { extra.0.visit_attributes(t, xs)? }
    //   ( ⟨qual_identifier ⟩ ⟨term⟩+ )
    term ::= LeftParen qual_identifier(id) terms(xs) RightParen { extra.0.visit_application(id, xs)? }

    terms ::= term(x) { vec![x] }
    terms ::= terms(mut xs) term(x) { xs.push(x); xs }

    // prop_literal ::= ⟨symbol⟩ | ( not ⟨symbol⟩ )
    prop_literal ::= bound_symbol(x) { (x, true) }
    prop_literal ::= LeftParen Symbol(s) bound_symbol(x) RightParen {
        if s != "not" {
            return Err(extra.0.parsing_error(extra.1.clone(), format!("invalid prop_literal: found {} instead of `not`", s)));
        }
        (x, false)
    }

    prop_literals ::= prop_literal(x) { vec![x] }
    prop_literals ::= prop_literals(mut xs) prop_literal(x) { xs.push(x); xs }

    // ⟨selector_dec⟩ ::= ( ⟨symbol⟩ ⟨sort⟩ )
    selector_dec ::= LeftParen fresh_symbol(x) sort(s) RightParen { (x, s) }

    selector_decs ::= selector_dec(x) { vec![x] }
    selector_decs ::= selector_decs(mut xs) selector_dec(x) { xs.push(x); xs }

    // constructor_dec ::= ( ⟨symbol⟩ ⟨selector_dec⟩∗ )
    constructor_dec ::= LeftParen fresh_symbol(x) selector_decs?(xs) RightParen
    {
        visitors::ConstructorDec { symbol:x, selectors:xs.unwrap_or_default() }
    }

    constructor_decs ::= constructor_dec(x) { vec![x] }
    constructor_decs ::= constructor_decs(mut xs) constructor_dec(x) { xs.push(x); xs }

    // datatype_dec ::= ( ⟨constructor_dec⟩+ ) | ( par ( ⟨symbol⟩+ ) ( ⟨constructor_dec⟩+ ) )
    datatype_dec ::= LeftParen constructor_decs(xs) RightParen
    {
        visitors::DatatypeDec { parameters: Vec::new(), constructors: xs }
    }
    datatype_dec ::= LeftParen Par LeftParen fresh_symbols(ps) RightParen LeftParen constructor_decs(xs) RightParen RightParen
    {
        visitors::DatatypeDec { parameters: ps, constructors: xs }
    }

    datatype_decs ::= datatype_dec(x) { vec![x] }
    datatype_decs ::= datatype_decs(mut xs) datatype_dec(x) { xs.push(x); xs }

    // function_dec ::= ⟨symbol⟩ ( ⟨sorted_var⟩∗ ) ⟨sort⟩
    function_dec ::= fresh_symbol(x) LeftParen sorted_vars?(xs) RightParen sort(s)
    {
        visitors::FunctionDec {
            name: x,
            parameters: xs.unwrap_or_default(),
            result: s,
        }
    }

    function_decs ::= function_dec(x) { vec![x] }
    function_decs ::= function_decs(mut xs) function_dec(x) { xs.push(x); xs }

    // sort_dec ::= ( ⟨symbol⟩ ⟨numeral⟩ )
    sort_dec ::= LeftParen fresh_symbol(x) Numeral(num) RightParen { (x, num) }

    sort_decs ::= sort_dec(x) { vec![x] }
    sort_decs ::= sort_decs(mut xs) sort_dec(x) { xs.push(x); xs }

    // command ::= ...
    //   ( assert ⟨term⟩ )
    command ::= LeftParen Assert term(t) RightParen { extra.0.visit_assert(t)? }
    //   ( check-sat )
    command ::= LeftParen CheckSat RightParen { extra.0.visit_check_sat()? }
    //   ( check-sat-assuming ( ⟨prop_literal⟩∗ ) )
    command ::= LeftParen CheckSatAssuming LeftParen prop_literals?(xs) RightParen RightParen
    {
        extra.0.visit_check_sat_assuming(xs.unwrap_or_default())?
    }
    //   ( declare-const ⟨symbol⟩ ⟨sort⟩ )
    command ::= LeftParen DeclareConst fresh_symbol(x) sort(s) RightParen
    {
        extra.0.visit_declare_const(x, s)?
    }
    //   ( declare-datatype ⟨symbol⟩ ⟨datatype_dec⟩)
    command ::= LeftParen DeclareDatatype fresh_symbol(s) datatype_dec(d) RightParen
    {
        extra.0.visit_declare_datatype(s, d)?
    }
    //   ( declare-datatypes ( ⟨sort_dec⟩n+1 ) ( ⟨datatype_dec⟩n+1 ) )
    command ::= LeftParen DeclareDatatypes LeftParen sort_decs(sorts) RightParen LeftParen datatype_decs(datatypes) RightParen RightParen
    {
        if sorts.len() == datatypes.len() {
            let results = sorts
                .into_iter()
                .zip(datatypes.into_iter())
                .map(|((sort, arity), datatype)| (sort, arity, datatype))
                .collect::<Vec<_>>();
            extra.0.visit_declare_datatypes(results)?
        } else {
            return Err(extra.0.parsing_error(extra.1.clone(), format!("wrong number of types in `declare-datatypes`: {} instead of {}", datatypes.len(), sorts.len())));
        }
    }
    //   ( declare-fun ⟨symbol⟩ ( ⟨sort⟩∗ ) ⟨sort⟩ )
    command ::= LeftParen DeclareFun fresh_symbol(x) LeftParen sorts?(xs) RightParen sort(r) RightParen
    {
        extra.0.visit_declare_fun(x, xs.unwrap_or_default(), r)?
    }
    //   ( declare-sort ⟨symbol⟩ ⟨numeral⟩ )
    command ::= LeftParen DeclareSort fresh_symbol(x) Numeral(num) RightParen
    {
        extra.0.visit_declare_sort(x, num)?
    }
    //   ( define-fun ⟨function_dec⟩ ⟨term⟩ )
    command ::= LeftParen DefineFun function_dec(d) term(x) RightParen
    {
        extra.0.visit_define_fun(d, x)?
    }
    //   ( define-fun-rec ⟨function_dec⟩ ⟨term⟩ )
    command ::= LeftParen DefineFunRec function_dec(d) term(x) RightParen
    {
        extra.0.visit_define_fun_rec(d, x)?
    }
    //   ( define-funs-rec ( ( ⟨function_dec⟩ )n+1 ) ( ⟨term⟩n+1 ) )
    command ::= LeftParen DefineFunsRec LeftParen function_decs(sigs) RightParen LeftParen terms(xs) RightParen RightParen
    {
        if sigs.len() == xs.len() {
            let defs = sigs.into_iter().zip(xs.into_iter()).collect::<Vec<_>>();
            extra.0.visit_define_funs_rec(defs)?
        } else {
            return Err(extra.0.parsing_error(extra.1.clone(), format!("wrong number of function bodies in `define-funs-rec`: {} instead of {}", xs.len(), sigs.len())));
        }
    }
    //   ( define-sort ⟨symbol⟩ ( ⟨symbol⟩∗ ) ⟨sort⟩ )
    command ::= LeftParen DefineSort fresh_symbol(x) LeftParen fresh_symbols?(xs) RightParen sort(r) RightParen
    {
        extra.0.visit_define_sort(x, xs.unwrap_or_default(), r)?
    }
    //   ( echo ⟨string⟩ )
    command ::= LeftParen Echo String(x) RightParen { extra.0.visit_echo(x)? }
    //   ( exit )
    command ::= LeftParen Exit RightParen { extra.0.visit_exit()? }
    //   ( get-assertions )
    command ::= LeftParen GetAssertions RightParen { extra.0.visit_get_assertions()? }
    //   ( get-assignment )
    command ::= LeftParen GetAssignment RightParen { extra.0.visit_get_assignment()? }
    //   ( get-info ⟨info_flag⟩ )
    command ::= LeftParen GetInfo keyword(x) RightParen { extra.0.visit_get_info(x)? }
    //   ( get-model )
    command ::= LeftParen GetModel RightParen { extra.0.visit_get_model()? }
    //   ( get-option ⟨keyword⟩ )
    command ::= LeftParen GetOption keyword(x) RightParen { extra.0.visit_get_option(x)? }
    //   ( get-proof )
    command ::= LeftParen GetProof RightParen { extra.0.visit_get_proof()? }
    //   ( get-unsat-assumptions )
    command ::= LeftParen GetUnsatAssumptions RightParen { extra.0.visit_get_unsat_assumptions()? }
    //   ( get-unsat-core )
    command ::= LeftParen GetUnsatCore RightParen { extra.0.visit_get_unsat_core()? }
    // Amazon update: fix parsing of get-value
    //   ( get-value ( ⟨term⟩+ ) )
    command ::= LeftParen GetValue LeftParen terms(xs) RightParen RightParen { extra.0.visit_get_value(xs)? }
    // end of Amazon update
    //   ( pop ⟨numeral⟩ )
    command ::= LeftParen Pop Numeral(x) RightParen { extra.0.visit_pop(x)? }
    //   ( push ⟨numeral⟩ )
    command ::= LeftParen Push Numeral(x) RightParen { extra.0.visit_push(x)? }
    //   ( reset )
    command ::= LeftParen Reset RightParen { extra.0.visit_reset()? }
    //   ( reset-assertions )
    command ::= LeftParen ResetAssertions RightParen { extra.0.visit_reset_assertions()? }
    //   ( set-info ⟨attribute⟩ )
    command ::= LeftParen SetInfo keyword(k) attribute_value(v) RightParen { extra.0.visit_set_info(k, v)? }
    //   ( set-logic ⟨symbol⟩ )
    command ::= LeftParen SetLogic bound_symbol(x) RightParen { extra.0.visit_set_logic(x)? }
    //   ( set-option ⟨attribute⟩ )
    command ::= LeftParen SetOption keyword(k) attribute_value(v) RightParen { extra.0.visit_set_option(k, v)? }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::smt2parser::{concrete::*, lexer::Lexer};

    pub(crate) fn parse_tokens<I: IntoIterator<Item = Token>>(tokens: I) -> Result<Command, Error> {
        let mut builder = SyntaxBuilder;
        let mut position = crate::smt2parser::Position::default();
        let mut p = Parser::new((&mut builder, &mut position));
        for token in tokens.into_iter() {
            p.parse(token)?;
        }
        Ok(p.end_of_input()?.0)
    }

    #[test]
    fn test_echo() {
        let value = parse_tokens(vec![
            Token::LeftParen,
            Token::Echo("echo".into()), // Amazon update
            Token::String("foo".into()),
            Token::RightParen,
        ])
        .unwrap();
        assert_eq!(
            value,
            Command::Echo {
                message: "foo".into()
            }
        );
    }

    #[test]
    fn test_assert_term() {
        let value = parse_tokens(Lexer::new(&b"(assert 12)"[..])).unwrap();
        assert_eq!(
            value,
            Command::Assert {
                term: Term::Constant(Constant::Numeral(num::BigUint::from(12u32))),
            }
        );

        let value = parse_tokens(Lexer::new(&b"(assert (as A B))"[..])).unwrap();
        assert_eq!(
            value,
            Command::Assert {
                term: Term::QualIdentifier(QualIdentifier::Sorted {
                    identifier: Identifier::Simple {
                        symbol: Symbol("A".into())
                    },
                    sort: Sort::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("B".into())
                        }
                    },
                })
            },
        );

        let value = parse_tokens(Lexer::new(&b"(assert (let ((x (f x 2))) (= x 3)))"[..])).unwrap();
        assert_eq!(
            value,
            Command::Assert {
                term: Term::Let {
                    var_bindings: vec![(
                        Symbol("x".into()),
                        Term::Application {
                            qual_identifier: QualIdentifier::Simple {
                                identifier: Identifier::Simple {
                                    symbol: Symbol("f".into())
                                }
                            },
                            arguments: vec![
                                Term::QualIdentifier(QualIdentifier::Simple {
                                    identifier: Identifier::Simple {
                                        symbol: Symbol("x".into())
                                    }
                                }),
                                Term::Constant(Constant::Numeral(num::BigUint::from(2u32)))
                            ]
                        }
                    )],
                    term: Box::new(Term::Application {
                        qual_identifier: QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("=".into())
                            }
                        },
                        arguments: vec![
                            Term::QualIdentifier(QualIdentifier::Simple {
                                identifier: Identifier::Simple {
                                    symbol: Symbol("x".into())
                                }
                            }),
                            Term::Constant(Constant::Numeral(num::BigUint::from(3u32)))
                        ]
                    }),
                }
            }
        );

        let value = parse_tokens(Lexer::new(
            &b"(assert (forall ((x Bool) (y Int)) (f x y))\n ; dfg \n )"[..],
        ))
        .unwrap();
        assert!(matches!(
            value,
            Command::Assert {
                term: Term::Forall { .. }
            }
        ));

        let result = parse_tokens(Lexer::new(&b"(assert (forall () (f x y)))"[..]));
        assert!(result.is_err());

        let value = parse_tokens(Lexer::new(
            &b"(assert ( ;foo\n match 3 ( (x (+ x 2)) ) ))"[..],
        ))
        .unwrap();
        assert!(matches!(
            value,
            Command::Assert {
                term: Term::Match { .. }
            }
        ));

        let value = parse_tokens(Lexer::new(&b"(assert ( ! 3 :f 1 :g (a 3) ))"[..])).unwrap();
        assert!(matches!(
            value,
            Command::Assert {
                term: Term::Attributes { .. }
            }
        ));

        let value = parse_tokens(Lexer::new(&b"(assert ( f 1 2 3 ))"[..])).unwrap();
        assert!(matches!(
            value,
            Command::Assert {
                term: Term::Application { .. }
            }
        ));
    }

    #[test]
    fn test_declare_datatypes_with_comment() {
        let value = parse_tokens(Lexer::new(&b"(declare-datatypes ((T@$TypeValue 0)(T@$TypeValueArray 0)) ((($BooleanType ) ($IntegerType ) ($AddressType ) ($StrType ) ($VectorType (|t#$VectorType| T@$TypeValue) ) ($StructType (|name#$StructType| T@$TypeName) (|ts#$StructType| T@$TypeValueArray) ) ($TypeType ) ($ErrorType ) ) (($TypeValueArray (|v#$TypeValueArray| |T@[Int]$TypeValue|) (|l#$TypeValueArray| Int) ) ) ))"[..])).unwrap();

        assert!(matches!(value, Command::DeclareDatatypes { .. }));
        // Test syntax visiting while we're at it.
        let mut builder = crate::smt2parser::concrete::SyntaxBuilder;
        assert_eq!(value, value.clone().accept(&mut builder).unwrap());
    }

    // Amazon updates: new tests for fixes
    #[test]
    fn test_get_value() {
        let value = parse_tokens(Lexer::new(&b"(get-value ( a b ))"[..])).unwrap();

        assert!(matches!(value, Command::GetValue { .. }));
    }

    #[test]
    fn test_reserved_word_in_attribute() {
        let value = parse_tokens(Lexer::new(
            &b"(assert (! (> x y) :pattern (let ((a b)) b)))"[..],
        ))
        .unwrap();

        assert!(matches!(
            value,
            Command::Assert {
                term: Term::Attributes { .. }
            }
        ));
    }
    // end of updates

}
