//! Module with functionality for modernizing some string functions in SMTLIB.
//! This updates the notation from an older version of the SMTLIB language, to
//! the modern syntax compatible with CVC5.

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use amzn_smt_ir::fold::IntraLogicFolder;
use amzn_smt_ir::fold::SuperFold;

use amzn_smt_ir::{fold::Fold, logic::*, Command as IRCommand, ParseError, Script, Term as IRTerm};
use amzn_smt_ir::{IConst, ISymbol, IVar, Index, IUF};
use smt2parser::concrete::*;

use std::convert::Infallible;
use std::convert::TryInto;

type Term = IRTerm<ALL>;
type Command = IRCommand<Term>;

///
/// Build an iterator from an input buffer. The input is parsed as a list of commands
/// in SMT-LIB syntax.
///
pub fn parse(
    smtlib: impl std::io::BufRead,
) -> Result<impl Iterator<Item = Command>, ParseError<ALL>> {
    Ok(Script::<Term>::parse(smtlib)?.into_iter())
}

/// basic visitor; we are going to modernize some of the string functions
#[derive(Default)]
pub struct ModernizeStringsBuilder {
    logic: Option<String>,
    has_arith: bool,
}

/// Convert a string constant in the Z3 style to SMT-LIB
/// The Z3 style uses escape sequences that are not valid in SMT-LIB.
///
/// Z3          SMT-LIB
/// \x<hex> --> \u{<hex>} where <hex> is a sequence of two hexadecimal digits
/// \a      --> \u{07}
/// \b      --> \u{08}
/// \f      --> \u{0C}
/// \n      --> \u{0A}
/// \r      --> \u{0D}
/// \t      --> \u{09}
/// \v      --> \u{0B}
///
fn convert_z3escapes(s: &str) -> String {
    // small state machine to process the bytes of s
    enum State {
        Base,         // default state
        Esc,          // after '\'
        EscX,         // after '\x'
        EscHex(char), // EscHex(h) = state after '\xh (if h is an hexa digit)
    }

    let mut new_string = String::with_capacity(s.len());
    let mut state = State::Base;

    for c in s.chars() {
        match state {
            State::Base => {
                new_string.push(c);
                if c == '\\' {
                    state = State::Esc;
                }
            }

            State::Esc => match c {
                'x' => state = State::EscX,
                'a' => {
                    new_string.push_str("u{07}");
                    state = State::Base;
                }
                'b' => {
                    new_string.push_str("u{08}");
                    state = State::Base;
                }
                'f' => {
                    new_string.push_str("u{0C}");
                    state = State::Base;
                }
                'n' => {
                    new_string.push_str("u{0A}");
                    state = State::Base;
                }
                'r' => {
                    new_string.push_str("u{0D}");
                    state = State::Base;
                }
                't' => {
                    new_string.push_str("u{09}");
                    state = State::Base;
                }
                'v' => {
                    new_string.push_str("u{0B}");
                    state = State::Base;
                }
                _ => {
                    new_string.push(c);
                    state = State::Base;
                }
            },

            State::EscX => {
                if c.is_ascii_hexdigit() {
                    state = State::EscHex(c);
                } else {
                    new_string.push('x');
                    new_string.push(c);
                    state = State::Base;
                }
            }

            State::EscHex(x) => {
                if c.is_ascii_hexdigit() {
                    new_string.push_str("u{");
                    new_string.push(x);
                    new_string.push(c);
                    new_string.push('}');
                } else {
                    new_string.push('x');
                    new_string.push(x);
                    new_string.push(c);
                };
                state = State::Base;
            }
        }
    }

    // handle any unfinished escape sequence (keep it unchanged)
    match state {
        State::EscX => new_string.push('x'),
        State::EscHex(x) => {
            new_string.push('x');
            new_string.push(x);
        }
        _ => {}
    }

    new_string
}

impl IntraLogicFolder<ALL> for ModernizeStringsBuilder {
    type Error = Infallible;

    fn fold_const(&mut self, constant: IConst) -> Result<Term, Self::Error> {
        Ok(match constant.as_ref() {
            Constant::String(s) => Constant::String(convert_z3escapes(s)).into(),
            _ => constant.into(),
        })
    }

    fn fold_var(&mut self, var: IVar) -> Result<Term, Self::Error> {
        Ok(match var.sym().0.as_str() {
            "re.nostr" => StringOp::ReNone.into(),
            _ => var.into(),
        })
    }

    /// visit function applications, and transform if necessary
    fn fold_uninterpreted_func(&mut self, t: IUF<ALL>) -> Result<Term, Self::Error> {
        let t = t.super_fold_with(self)?;
        // now, process the term
        Ok(match t.func.0.as_str() {
            "str.to.re" => {
                // turn str.to.re into str.to_re
                StringOp::ToRe(t.args[0].clone()).into()
            }
            "str.in.re" => {
                // turn str.in.re into str.in_re
                let (y, x) = (t.args[1].clone(), t.args[0].clone());
                StringOp::InRe(x, y).into()
            }
            "str.to.int" => {
                // turn str.to.int into str.to_int
                StringOp::ToInt(t.args[0].clone()).into()
            }
            "int.to.str" => {
                // turn int.to.str into str.from_int
                StringOp::FromInt(t.args[0].clone()).into()
            }
            "re.loop" => {
                // turn: (re.loop (re.range "0" "9") 12 12)
                // into: ( (_ re.loop 12 12) (re.range "0" "9"))
                let indices = t.args[1..3]
                    .iter()
                    .map(|ind| {
                        if let Term::Constant(n) = ind {
                            if let Constant::Numeral(n) = n.as_ref() {
                                return Index::Numeral(n.clone()).into();
                            }
                        }
                        panic!("{:?}", ind);
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .expect("Invalid re.loop parameters");

                StringOp::ReLoop(indices, t.args[0].clone()).into()
            }
            "+" | "-" | ">" | "<" | ">=" | "<=" | "*" => {
                self.has_arith = true;
                t.into()
            }
            _ => t.into(),
        })
    }

    fn fold_set_logic(&mut self, logic: ISymbol) -> Result<Command, Self::Error> {
        self.logic = Some(logic.0.clone());
        Ok(Command::SetLogic { symbol: logic })
    }
}

/// Convert an SMT input that uses the Z3 (old) syntax for string constraints
/// into an SMT-LIB compliant version.
pub fn modernize_string_fcts(commands: impl Iterator<Item = Command>) -> Vec<Command> {
    let mut modernize_builder = ModernizeStringsBuilder::default();

    // visit the AST, modernizing the relevant string functions
    let mut v = commands
        .map(|c| c.fold_with(&mut modernize_builder))
        .collect::<Result<Vec<Command>, _>>()
        .unwrap();

    // Guess the logic and add a (set-logic ..) command if it's missing.
    // To be safe, we insert the (set-logic ..) after any (set-option ...) commands.
    if modernize_builder.logic.is_none() && !v.is_empty() {
        let guess = if modernize_builder.has_arith {
            "QF_SLIA"
        } else {
            "QF_S"
        };
        let mut i = 0;
        while let Command::SetOption { .. } = v[i] {
            i += 1;
        }
        v.insert(
            i,
            Command::SetLogic {
                symbol: ISymbol::from(guess.to_string()),
            },
        );
    };

    v
}
