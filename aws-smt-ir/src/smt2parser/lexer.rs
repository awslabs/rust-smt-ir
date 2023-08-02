// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

// Modifications: Copyright (c) Amazon.com, Inc. or its affiliates. All Rights Reserved.
// Better error detection and reporting

//! Lexing primitives.

use std::{fmt::Display, io::Error};

use crate::smt2parser::{parser::Token, Decimal, Numeral};
use num::{BigInt, Num};

/// Record a position in the input stream.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct Position {
    pub path: Option<String>,
    pub line: usize,
    pub column: usize,
}

impl Position {
    pub fn new(path: Option<String>, line: usize, column: usize) -> Self {
        Self { path, line, column }
    }
}

impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.path {
            Some(path) => write!(f, "{}:{}:{}", path, self.line, self.column),
            None => write!(f, "{}:{}", self.line, self.column),
        }
    }
}

// Amazon updates
// 1) lexer errors are converted to BadToken
// 2) implement the Display trait for Tokens
// 3) store errors and EOI marked in Lexer struct

// Error tokens
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BadToken {
    AllGood,
    BadQuotedSymbol,
    UnclosedString,
    BadBinaryLiteral,
    BadHexLiteral,
    BadSharp,
    BadNumeral,
    NonUtf8Symbol,
    NonUtf8String,
    NonUtf8Keyword,
    Error,
}

impl Display for BadToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BadToken::AllGood => "all good",
            BadToken::BadQuotedSymbol => "missing '|' in quoted symbol",
            BadToken::UnclosedString => "unterminated string literal",
            BadToken::BadBinaryLiteral => "invalid binary literal",
            BadToken::BadHexLiteral => "invalid hexadecimal literal",
            BadToken::BadSharp => "invalid token near '#'",
            BadToken::BadNumeral => "invalid numeral",
            BadToken::NonUtf8Symbol => "symbol is not UTF8",
            BadToken::NonUtf8String => "string is not UTF8",
            BadToken::NonUtf8Keyword => "keyword is not UTF8",
            BadToken::Error => "bad input",
        }
        .fmt(f)
    }
}

//
// Token formatter
//
fn fmt_symbol(s: &str, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    fn is_symbol_char(c: char) -> bool {
        c.is_ascii() && is_symbol_byte(c as u8)
    }
    fn needs_quotes(s: &str) -> bool {
        s.is_empty()
            || s.chars().any(|c| !is_symbol_char(c))
            || s.chars().next().unwrap().is_ascii_digit()
    }
    if needs_quotes(s) {
        write!(f, "|{}|", s)
    } else {
        write!(f, "{}", s)
    }
}

fn fmt_decimal(d: &Decimal, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    // d is non-negative
    let mut aux = d.clone();
    let mut shift = 0u32 as usize;
    while !aux.is_integer() {
        aux *= BigInt::from(10);
        shift += 1;
    }
    // shift is the number of digits after .
    // aux is d * 10^shift
    if shift == 0 {
        write!(f, "{}.0", aux)
    } else {
        let mut s = aux.to_string();
        if shift >= s.len() {
            write!(f, "0.")?;
            while shift > s.len() {
                write!(f, "0")?;
                shift -= 1;
            }
        } else {
            s.insert(s.len() - shift, '.');
        }
        s.fmt(f)
    }
}

fn fmt_string(s: &str, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "\"")?;
    for c in s.chars() {
        if c == '"' {
            write!(f, "\"\"")?;
        } else {
            write!(f, "{}", c)?;
        }
    }
    write!(f, "\"")
}

fn fmt_hexadecimal(x: &[u8], f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "#x")?;
    for hex in x {
        write!(f, "{:x}", hex)?;
    }
    Ok(())
}

fn fmt_binary(x: &[bool], f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "#b")?;
    for &bit in x {
        write!(f, "{}", if bit { "1" } else { "0" })?
    }
    Ok(())
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Symbol(x) => fmt_symbol(x, f),
            Token::Keyword(x) => write!(f, ":{}", x),
            Token::Numeral(x) => write!(f, "{}", x),
            Token::Decimal(x) => fmt_decimal(x, f),
            Token::Hexadecimal(x) => fmt_hexadecimal(x, f),
            Token::Binary(x) => fmt_binary(x, f),
            Token::String(s) => fmt_string(s, f),
            Token::LeftParen => "(".fmt(f),
            Token::RightParen => ")".fmt(f),
            Token::Underscore(s) => s.fmt(f),
            Token::Exclam(s) => s.fmt(f),
            Token::As(s) => s.fmt(f),
            Token::Let(s) => s.fmt(f),
            Token::Exists(s) => s.fmt(f),
            Token::Forall(s) => s.fmt(f),
            Token::Match(s) => s.fmt(f),
            Token::Par(s) => s.fmt(f),
            Token::Assert(s) => s.fmt(f),
            Token::CheckSat(s) => s.fmt(f),
            Token::CheckSatAssuming(s) => s.fmt(f),
            Token::DeclareConst(s) => s.fmt(f),
            Token::DeclareDatatype(s) => s.fmt(f),
            Token::DeclareDatatypes(s) => s.fmt(f),
            Token::DeclareFun(s) => s.fmt(f),
            Token::DeclareSort(s) => s.fmt(f),
            Token::DefineFun(s) => s.fmt(f),
            Token::DefineFunRec(s) => s.fmt(f),
            Token::DefineFunsRec(s) => s.fmt(f),
            Token::DefineSort(s) => s.fmt(f),
            Token::Echo(s) => s.fmt(f),
            Token::Exit(s) => s.fmt(f),
            Token::GetAssertions(s) => s.fmt(f),
            Token::GetAssignment(s) => s.fmt(f),
            Token::GetInfo(s) => s.fmt(f),
            Token::GetModel(s) => s.fmt(f),
            Token::GetOption(s) => s.fmt(f),
            Token::GetProof(s) => s.fmt(f),
            Token::GetUnsatAssumptions(s) => s.fmt(f),
            Token::GetUnsatCore(s) => s.fmt(f),
            Token::GetValue(s) => s.fmt(f),
            Token::Pop(s) => s.fmt(f),
            Token::Push(s) => s.fmt(f),
            Token::Reset(s) => s.fmt(f),
            Token::ResetAssertions(s) => s.fmt(f),
            Token::SetInfo(s) => s.fmt(f),
            Token::SetLogic(s) => s.fmt(f),
            Token::SetOption(s) => s.fmt(f),
        }
    }
}
// end Amazon updates

pub(crate) struct Lexer<R> {
    reader: R,
    reserved_words: Vec<Token>,
    reserved_words_map: fst::Map<Vec<u8>>,
    current_offset: usize,
    current_line: usize,
    current_column: usize,

    // Amazon updates
    read_error: Option<Error>, // Read error or None
    bad_token: BadToken,       // Lexer error
    done: bool,                // End of input
}

// Amazon update: changed the type of keywords (cf. parser.rs)
#[allow(clippy::type_complexity)]
const KEYWORDS: &[(&str, fn(String) -> Token)] = {
    use Token::*;
    &[
        ("_", Underscore),
        ("!", Exclam),
        ("as", As),
        ("let", Let),
        ("exists", Exists),
        ("forall", Forall),
        ("match", Match),
        ("par", Par),
        ("assert", Assert),
        ("check-sat", CheckSat),
        ("check-sat-assuming", CheckSatAssuming),
        ("declare-const", DeclareConst),
        ("declare-datatype", DeclareDatatype),
        ("declare-datatypes", DeclareDatatypes),
        ("declare-fun", DeclareFun),
        ("declare-sort", DeclareSort),
        ("define-fun", DefineFun),
        ("define-fun-rec", DefineFunRec),
        ("define-funs-rec", DefineFunsRec),
        ("define-sort", DefineSort),
        ("echo", Echo),
        ("exit", Exit),
        ("get-assertions", GetAssertions),
        ("get-assignment", GetAssignment),
        ("get-info", GetInfo),
        ("get-model", GetModel),
        ("get-option", GetOption),
        ("get-proof", GetProof),
        ("get-unsat-assumptions", GetUnsatAssumptions),
        ("get-unsat-core", GetUnsatCore),
        ("get-value", GetValue),
        ("pop", Pop),
        ("push", Push),
        ("reset", Reset),
        ("reset-assertions", ResetAssertions),
        ("set-info", SetInfo),
        ("set-logic", SetLogic),
        ("set-option", SetOption),
    ]
};
// end Amazon updates

impl<R> Lexer<R>
where
    R: std::io::BufRead,
{
    pub(crate) fn new(reader: R) -> Self {
        let (reserved_words, reserved_words_map) = Self::make_reserved_words();
        Self {
            reader,
            reserved_words,
            reserved_words_map,
            current_offset: 0,
            current_line: 0,
            current_column: 0,
            // Amazon updates
            read_error: None,
            bad_token: BadToken::AllGood,
            done: false,
            // end of updates
        }
    }

    #[inline]
    fn lookup_symbol(&self, s: &[u8]) -> Option<&Token> {
        self.reserved_words_map
            .get(s)
            .map(|index| &self.reserved_words[index as usize])
    }

    fn make_reserved_words() -> (Vec<Token>, fst::Map<Vec<u8>>) {
        let mut keywords = KEYWORDS.to_vec();
        keywords.sort_by_key(|(key, _)| key.to_string());
        let mut words = Vec::new();
        for (s, f) in &keywords {
            words.push(f(s.to_string())) // Amazon update
        }
        let map = fst::Map::from_iter(
            keywords
                .iter()
                .enumerate()
                .map(|(index, (key, _))| (key, index as u64)),
        )
        .expect("Failed to create reserved token map");
        (words, map)
    }

    #[cfg(test)]
    pub(crate) fn current_offset(&self) -> usize {
        self.current_offset
    }

    #[cfg(test)]
    pub(crate) fn current_column(&self) -> usize {
        self.current_column
    }

    #[cfg(test)]
    pub(crate) fn current_line(&self) -> usize {
        self.current_line
    }

    #[inline]
    pub(crate) fn update_position(&self, pos: &mut Position) {
        pos.line = self.current_line + 1;
        pos.column = self.current_column + 1;
    }

    fn consume_byte(&mut self) {
        if let Some(c) = self.peek_byte() {
            if *c == b'\n' {
                self.current_line += 1;
                self.current_column = 0;
            } else {
                self.current_column += 1;
            }
            self.current_offset += 1;
            self.reader.consume(1)
        }
    }

    fn read_byte(&mut self) -> Option<u8> {
        let c = self.peek_byte().cloned();
        self.consume_byte();
        c
    }

    #[inline]
    fn peek_bytes(&mut self) -> &[u8] {
        // Amazon updates:
        //
        // Once we've reached EOI, we don't want to call fill_buf() again.
        // Because fill_buf() will try to read more bytes after EOI,
        // which gives a weird behavior (e.g., if reading from a terminal).
        //
        // Also catch read errors from fill_buf() rather than panic
        //
        if self.done {
            &[]
        } else {
            match self.reader.fill_buf() {
                Ok(&[]) => {
                    self.done = true;
                    &[]
                }
                Ok(b) => b,
                Err(e) => {
                    self.read_error = Some(e);
                    &[]
                }
            }
        }
        // end of updates
    }

    fn peek_byte(&mut self) -> Option<&u8> {
        self.peek_bytes().first()
    }

    fn skip_whitespace(&mut self) -> bool {
        match self.peek_byte() {
            Some(b) if matches!(b, b' ' | b'\n' | b'\t' | b'\r') => {
                self.consume_byte();
                true
            }
            _ => false,
        }
    }

    fn skip_comment(&mut self) -> bool {
        match self.peek_byte() {
            Some(c) if *c == b';' => {
                self.consume_byte();
                while let Some(c) = self.read_byte() {
                    if c == b'\n' {
                        break;
                    }
                }
                true
            }
            _ => false,
        }
    }
}

impl<R> Iterator for Lexer<R>
where
    R: std::io::BufRead,
{
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        while self.skip_whitespace() || self.skip_comment() {}
        match self.peek_byte() {
            // Parentheses
            Some(b'(') => {
                self.consume_byte();
                Some(Token::LeftParen)
            }
            Some(b')') => {
                self.consume_byte();
                Some(Token::RightParen)
            }
            // Quoted symbols
            Some(b'|') => {
                self.consume_byte();
                let mut content = Vec::new();
                while let Some(c) = self.read_byte() {
                    if c == b'|' {
                        return match String::from_utf8(content) {
                            Ok(s) => Some(Token::Symbol(s)),
                            Err(_) => {
                                self.bad_token = BadToken::NonUtf8Symbol; // Amazon update
                                None
                            }
                        };
                    }
                    content.push(c);
                }
                // Do not accept EOI as a terminator.
                self.bad_token = BadToken::BadQuotedSymbol; // Amazon update
                None
            }
            // String literals
            Some(b'"') => {
                self.consume_byte();
                let mut content = Vec::new();
                while let Some(c) = self.read_byte() {
                    if c == b'"' {
                        if let Some(d) = self.peek_byte() {
                            if *d == b'"' {
                                self.consume_byte();
                                content.push(b'"');
                                continue;
                            }
                        }
                        return match String::from_utf8(content) {
                            Ok(s) => Some(Token::String(s)),
                            Err(_) => {
                                self.bad_token = BadToken::NonUtf8String; // Amazon update
                                None
                            }
                        };
                    }
                    content.push(c);
                }
                // Do not accept EOI as a terminator.
                self.bad_token = BadToken::UnclosedString; // Amazon update
                None
            }
            // Binary and Hexadecimal literals
            Some(b'#') => {
                self.consume_byte();
                match self.peek_byte() {
                    Some(b'b') => {
                        self.consume_byte();
                        let mut content = Vec::new();
                        while let Some(c) = self.peek_byte() {
                            match c {
                                b'0' => content.push(false),
                                b'1' => content.push(true),
                                _ => break,
                            }
                            self.consume_byte();
                        }
                        if content.is_empty() {
                            self.bad_token = BadToken::BadBinaryLiteral; // Amazon update
                            None
                        } else {
                            Some(Token::Binary(content))
                        }
                    }
                    Some(b'x') => {
                        self.consume_byte();
                        let mut content = Vec::new();
                        while let Some(c) = self.peek_byte() {
                            match c {
                                b'0'..=b'9' => content.push(c - b'0'),
                                b'a'..=b'f' => content.push(c - b'a' + 10),
                                b'A'..=b'F' => content.push(c - b'A' + 10),
                                _ => break,
                            }
                            self.consume_byte();
                        }
                        if content.is_empty() {
                            self.bad_token = BadToken::BadHexLiteral; // Amazon update
                            None
                        } else {
                            Some(Token::Hexadecimal(content))
                        }
                    }
                    _ => {
                        self.bad_token = BadToken::BadSharp;
                        None
                    }
                }
            }
            // Number literals
            Some(digit @ b'0'..=b'9') => {
                let mut numerator = vec![*digit];
                self.consume_byte();
                while let Some(c) = self.peek_byte() {
                    if !c.is_ascii_digit() {
                        break;
                    }
                    numerator.push(*c);
                    self.consume_byte();
                }
                if numerator.len() > 1 && numerator.starts_with(b"0") {
                    self.bad_token = BadToken::BadNumeral; // Amazon update
                    return None;
                }
                let numerator = String::from_utf8(numerator).unwrap();
                match self.peek_byte() {
                    Some(b'.') => {
                        self.consume_byte();
                        let mut denumerator = Vec::new();
                        while let Some(c) = self.peek_byte() {
                            if !c.is_ascii_digit() {
                                break;
                            }
                            denumerator.push(*c);
                            self.consume_byte();
                        }
                        if denumerator.is_empty() {
                            self.bad_token = BadToken::BadNumeral; // Amazon update
                            return None;
                        }
                        let denumerator = String::from_utf8(denumerator).unwrap();
                        let num =
                            num::BigInt::from_str_radix(&(numerator + &denumerator), 10).ok()?;
                        let denom = num::BigInt::from(10u32).pow(denumerator.len() as u32);
                        Some(Token::Decimal(Decimal::new(num, denom)))
                    }
                    _ => Some(Token::Numeral(
                        Numeral::from_str_radix(&numerator, 10).ok()?,
                    )),
                }
            }
            // Keywords
            Some(b':') => {
                self.consume_byte();
                let mut content = Vec::new();
                while let Some(c) = self.peek_byte() {
                    if !is_symbol_byte(*c) {
                        break;
                    }
                    content.push(*c);
                    self.consume_byte();
                }
                match String::from_utf8(content) {
                    Ok(s) => Some(Token::Keyword(s)),
                    Err(_) => {
                        self.bad_token = BadToken::NonUtf8Keyword; // Amazon update (We tolerate UTF8 even though SMT-LIB2 requires keywords to be all ascii).
                        None
                    }
                }
            }
            // Symbols (including `_` and `!`)
            Some(c) if is_non_digit_symbol_byte(*c) => {
                let mut content = vec![*c];
                self.consume_byte();
                while let Some(c) = self.peek_byte() {
                    if !is_symbol_byte(*c) {
                        break;
                    }
                    content.push(*c);
                    self.consume_byte();
                }
                match self.lookup_symbol(&content) {
                    Some(token) => Some(token.clone()),
                    None => match String::from_utf8(content) {
                        Ok(s) => Some(Token::Symbol(s)),
                        Err(_) => {
                            self.bad_token = BadToken::NonUtf8Symbol; // Amazon update
                            None
                        }
                    },
                }
            }
            // Error
            Some(_) => {
                self.bad_token = BadToken::Error;
                None
            }
            // EOI
            _ => None,
        }
    }
}

pub(crate) fn is_symbol_byte(c: u8) -> bool {
    c.is_ascii_digit() || is_non_digit_symbol_byte(c)
}

pub(crate) fn is_non_digit_symbol_byte(c: u8) -> bool {
    matches!(c,
        b'a'..=b'z'
        | b'A'..=b'Z'
        | b'~'
        | b'!'
        | b'@'
        | b'$'
        | b'%'
        | b'^'
        | b'&'
        | b'*'
        | b'_'
        | b'-'
        | b'+'
        | b'='
        | b'<'
        | b'>'
        | b'.'
        | b'?'
        | b'/')
}

#[test]
fn test_spaces() {
    let input = b"xx  \n asd ";
    let mut lexer = Lexer::new(&input[..]);
    let tokens: Vec<_> = (&mut lexer).collect();
    assert_eq!(
        tokens,
        vec![Token::Symbol("xx".into()), Token::Symbol("asd".into())]
    );
    assert_eq!(lexer.current_line(), 1);
    assert_eq!(lexer.current_column(), 5);
    assert_eq!(lexer.current_offset(), input.len());
}

#[test]
fn test_error() {
    let input = b"xx  \\";
    let mut lexer = Lexer::new(&input[..]);
    assert_eq!(
        (&mut lexer).collect::<Vec<_>>(),
        vec![Token::Symbol("xx".into())]
    );
    assert_eq!(lexer.current_line(), 0);
    assert_eq!(lexer.current_column(), input.len() - 1);
    assert_eq!(lexer.current_offset(), input.len() - 1);
}

#[test]
fn test_literals() {
    let lexer = Lexer::new(&b"135"[..]);
    assert_eq!(
        lexer.collect::<Vec<_>>(),
        vec![Token::Numeral(Numeral::from(135u32))]
    );

    let lexer = Lexer::new(&b"0"[..]);
    assert_eq!(
        lexer.collect::<Vec<_>>(),
        vec![Token::Numeral(Numeral::from(0u32))]
    );

    let lexer = Lexer::new(&b"(0 59)"[..]);
    assert_eq!(
        lexer.collect::<Vec<_>>(),
        vec![
            Token::LeftParen,
            Token::Numeral(Numeral::from(0u32)),
            Token::Numeral(Numeral::from(59u32)),
            Token::RightParen
        ]
    );

    let lexer = Lexer::new(&b"135"[..]);
    assert_eq!(
        lexer.collect::<Vec<_>>(),
        vec![Token::Numeral(Numeral::from(135u32))]
    );

    let lexer = Lexer::new(&b"135.2"[..]);
    assert_eq!(
        lexer.collect::<Vec<_>>(),
        vec![Token::Decimal(Decimal::from((
            1352u32.into(),
            10u32.into()
        )))]
    );

    let mut lexer = Lexer::new(&b"0135"[..]);
    assert!(lexer.next().is_none());

    let mut lexer = Lexer::new(&b"135."[..]);
    assert!(lexer.next().is_none());

    let lexer = Lexer::new(&b"#b101"[..]);
    assert_eq!(
        lexer.collect::<Vec<_>>(),
        vec![Token::Binary(vec![true, false, true])]
    );

    let lexer = Lexer::new(&b"#x1Ae"[..]);
    assert_eq!(
        lexer.collect::<Vec<_>>(),
        vec![Token::Hexadecimal(vec![1, 10, 14])]
    );

    let lexer = Lexer::new(&br#""acv""12""#[..]);
    assert_eq!(
        lexer.collect::<Vec<_>>(),
        vec![Token::String("acv\"12".into())]
    );

    let lexer = Lexer::new(&br#""acv12""#[..]);
    assert_eq!(
        lexer.collect::<Vec<_>>(),
        vec![Token::String("acv12".into())]
    );
}

#[test]
fn test_symbol() {
    let lexer = Lexer::new(&b"A$@135"[..]);
    assert_eq!(
        lexer.collect::<Vec<_>>(),
        vec![Token::Symbol("A$@135".into())]
    );

    let lexer = Lexer::new(&b"|135|"[..]);
    assert_eq!(lexer.collect::<Vec<_>>(), vec![Token::Symbol("135".into())]);
}

#[test]
fn test_keyword() {
    let lexer = Lexer::new(&b":A$@135"[..]);
    assert_eq!(
        lexer.collect::<Vec<_>>(),
        vec![Token::Keyword("A$@135".into())]
    );
}

// Amazon modifications: this test can fail depending on compiler version
//
// #[test]
// fn test_token_size() {
//     assert_eq!(std::mem::size_of::<Token>(), 72);
//     assert_eq!(std::mem::size_of::<Box<Token>>(), 8);
// }
