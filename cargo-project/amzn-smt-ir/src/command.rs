//! SMT-LIB Command representation adapted from [smt2parser](https://github.com/facebookincubator/smt2utils/blob/a3f631f9ab4599e8e800ef445a1bd9d24631582e/smt2parser/src/concrete.rs).
//! If [`smt2parser::concrete::Command`] could be made generic, this file wouldn't have to exist;
//! this change is requested in [smt2utils#36](https://github.com/facebookincubator/smt2utils/issues/36)
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{convert::Converter, *};
use std::{convert::TryFrom, fmt};

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Command<Term> {
    Assert(Term),
    CheckSat,
    CheckSatAssuming {
        literals: Vec<(ISymbol, bool)>,
    },
    DeclareConst {
        symbol: ISymbol,
        sort: ISort,
    },
    DeclareDatatype {
        symbol: ISymbol,
        datatype: DatatypeDec,
    },
    DeclareDatatypes {
        datatypes: Vec<(ISymbol, Numeral, DatatypeDec)>,
    },
    DeclareFun {
        symbol: ISymbol,
        parameters: Vec<ISort>,
        sort: ISort,
    },
    DeclareSort {
        symbol: ISymbol,
        arity: Numeral,
    },
    DefineFun {
        sig: FunctionDec,
        term: Term,
    },
    DefineFunRec {
        sig: FunctionDec,
        term: Term,
    },
    DefineFunsRec {
        funs: Vec<(FunctionDec, Term)>,
    },
    DefineSort {
        symbol: ISymbol,
        parameters: Vec<ISymbol>,
        sort: ISort,
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
        value: AttributeValue,
    },
    SetLogic {
        symbol: ISymbol,
    },
    SetOption {
        keyword: Keyword,
        value: AttributeValue,
    },
}

impl<Term: fmt::Display> fmt::Display for Command<Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Command::*;
        match self {
            Assert(term) => write!(f, "(assert {})", term),
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
                Constant::Numeral(arity.clone())
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
            Echo { message } => write!(f, "(echo {})", Constant::String(message.clone())),
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
            Pop { level } => write!(f, "(pop {})", Constant::Numeral(level.clone())),
            Push { level } => write!(f, "(push {})", Constant::Numeral(level.clone())),
            Reset => write!(f, "(reset)"),
            ResetAssertions => write!(f, "(reset-assertions)"),
            SetInfo { keyword, value } => write!(f, "(set-info {} {})", keyword, value),
            SetLogic { symbol } => write!(f, "(set-logic {})", symbol),
            SetOption { keyword, value } => write!(f, "(set-option {} {})", keyword, value),
        }
    }
}

impl<L: Logic> TryFrom<smt2parser::concrete::Command> for Command<Term<L>>
where
    QualIdentifier: Into<L::Var>,
{
    type Error = ParseError<L>;

    fn try_from(value: smt2parser::concrete::Command) -> Result<Self, Self::Error> {
        value.accept(&mut Converter::default())
    }
}
