// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

// Modifications: Copyright (c) Amazon.com, Inc. or its affiliates. All Rights Reserved.
// Summary of Amazon changes
// - import smt2parser as a module in aws_smt_ir
// - remove stats.rs and main.rs (not used here)
// - better error checking: detect read and lexer errors
// - fix the parser's get-value rule: the SMT syntax is ( get-value ( <term>+ ))
// - fix the parser to accept keywords in attribute s-expr
// - fix some compiler and clippy warnings

//! This crate provides a generic parser for SMT2 commands, as specified by the
//! [SMT-LIB-2 standard](http://smtlib.cs.uiowa.edu/language.shtml).
//!
//! Commands are parsed and immediately visited by a user-provided
//! implementation of the trait [`visitors::Smt2Visitor`].
//!
//! To obtain concrete syntax values, use [`concrete::SyntaxBuilder`] as a
//! visitor:
//! ```
//! # use aws_smt_ir::smt2parser::{CommandStream, concrete};
//! let input = b"(echo \"Hello world!\")(exit)";
//! let stream = CommandStream::new(
//!     &input[..],
//!     concrete::SyntaxBuilder,
//!     Some("optional/path/to/file".to_string()),
//! );
//! let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
//! assert!(matches!(commands[..], [
//!     concrete::Command::Echo {..},
//!     concrete::Command::Exit,
//! ]));
//! assert_eq!(commands[0].to_string(), "(echo \"Hello world!\")");
//! ```

#![forbid(unsafe_code)]

pub mod concrete;
mod lexer;
mod parser;
pub mod renaming;
pub mod rewriter;
pub mod visitors;

/// SMT2 numeral values.
pub type Numeral = num::bigint::BigUint;
/// SMT2 decimal values.
pub type Decimal = num::rational::BigRational;
/// A base-16 digit.
pub type Nibble = u8;
/// SMT2 hexadecimal values.
pub type Hexadecimal = Vec<Nibble>;
/// SMT2 binary values.
pub type Binary = Vec<bool>;

/// A minimal error type.
pub use concrete::Error;
/// A position in the input.
pub use lexer::Position;

/// Parse the input data and return a stream of interpreted SMT2 commands
pub struct CommandStream<R, T>
where
    R: std::io::BufRead,
    T: visitors::Smt2Visitor,
{
    lexer: lexer::Lexer<R>,
    visitor: T,
    position: Position,
    got_an_error: bool, // Amazon update: set to true after the first error
}

impl<R, T> CommandStream<R, T>
where
    R: std::io::BufRead,
    T: visitors::Smt2Visitor,
{
    pub fn new(reader: R, visitor: T, path: Option<String>) -> Self {
        Self {
            lexer: lexer::Lexer::new(reader),
            visitor,
            position: Position {
                path,
                ..Position::default()
            },
            got_an_error: false, // Amazon update
        }
    }

    pub fn visitor(&self) -> &T {
        &self.visitor
    }

    pub fn visitor_mut(&mut self) -> &mut T {
        &mut self.visitor
    }

    pub fn into_visitor(self) -> T {
        self.visitor
    }
}

impl<R, T> Iterator for CommandStream<R, T>
where
    R: std::io::BufRead,
    T: visitors::Smt2Visitor,
{
    type Item = Result<T::Command, T::Error>;

    #[allow(clippy::while_let_on_iterator)]
    fn next(&mut self) -> Option<Result<T::Command, T::Error>> {
        // Amazon update
        if self.got_an_error {
            // we don't want to loop after an error
            return None;
        }
        // end of update
        let mut parser = parser::Parser::new((&mut self.visitor, &mut self.position));
        let mut unmatched_paren = 0;
        while let Some(token) = self.lexer.next() {
            match &token {
                parser::Token::LeftParen => unmatched_paren += 1,
                parser::Token::RightParen => {
                    if unmatched_paren > 0 {
                        unmatched_paren -= 1;
                    }
                }
                _ => (),
            }
            self.lexer.update_position(parser.extra_mut().1);
            if let Err(err) = parser.parse(token) {
                self.got_an_error = true; // Amazon update: stop after the first error
                return Some(Err(err));
            }
            if unmatched_paren == 0 {
                return match parser.end_of_input() {
                    Ok((command, _)) => Some(Ok(command)),
                    Err(err) => {
                        self.got_an_error = true;
                        Some(Err(err))
                    }
                };
            }
        }
        if unmatched_paren > 0 {
            // We ran out of valid tokens in the middle of a command.
            let extra = parser.into_extra();
            Some(Err(extra.0.parsing_error(
                extra.1.clone(),
                "unexpected end of input".into(),
            )))
        } else {
            // There are no more valid tokens to parse.
            // TODO: report invalid tokens as an error.
            None
        }
    }
}

#[test]
fn test_command_stream_error() {
    let input = b"(echo \"Hello world!\")(exit f)";
    let builder = concrete::SyntaxBuilder;
    let stream = CommandStream::new(&input[..], builder, None);
    let commands = stream.collect::<Vec<_>>();
    assert!(matches!(
        commands[..],
        [
            Ok(concrete::Command::Echo { .. }),
            Err(concrete::Error::SyntaxError(..)),
            // Err(concrete::Error::SyntaxError(..)), Amazon update: stop parsing after the first error
        ]
    ));
    assert_eq!(
        commands[0].as_ref().unwrap().to_string(),
        "(echo \"Hello world!\")"
    );
}

#[test]
fn test_command_stream_invalid_token() {
    let input = b"(echo \"Hello world!\")(exit \x0000)";
    let builder = concrete::SyntaxBuilder;
    let stream = CommandStream::new(&input[..], builder, None);
    let commands = stream.collect::<Vec<_>>();
    assert!(matches!(
        commands[..],
        [
            Ok(concrete::Command::Echo { .. }),
            Err(concrete::Error::ParsingError(..)),
        ]
    ));
    assert_eq!(
        commands[0].as_ref().unwrap().to_string(),
        "(echo \"Hello world!\")"
    );
}
