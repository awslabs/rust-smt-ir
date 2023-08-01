// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

// Modifications: Copyright (c) Amazon.com, Inc. or its affiliates. All Rights Reserved.

//! Lexing primitives.

use crate::smt2parser::{parser::Token, Decimal, Numeral};
use num::Num;

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

pub(crate) struct Lexer<R> {
    reader: R,
    reserved_words: Vec<Token>,
    reserved_words_map: fst::Map<Vec<u8>>,
    current_offset: usize,
    current_line: usize,
    current_column: usize,
}

const KEYWORDS: &[(&str, Token)] = {
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
        for (_, token) in &keywords {
            words.push(token.clone());
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
        self.reader
            .fill_buf()
            .expect("Error while reading input stream")
    }

    fn peek_byte(&mut self) -> Option<&u8> {
        self.peek_bytes().get(0)
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
                            Err(_) => None,
                        };
                    }
                    content.push(c);
                }
                // Do not accept EOI as a terminator.
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
                            Err(_) => None,
                        };
                    }
                    content.push(c);
                }
                // Do not accept EOI as a terminator.
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
                            None
                        } else {
                            Some(Token::Hexadecimal(content))
                        }
                    }
                    _ => None,
                }
            }
            // Number literals
            Some(digit @ b'0'..=b'9') => {
                let mut numerator = vec![*digit];
                self.consume_byte();
                while let Some(c) = self.peek_byte() {
                    if !is_digit_byte(*c) {
                        break;
                    }
                    numerator.push(*c);
                    self.consume_byte();
                }
                if numerator.len() > 1 && numerator.starts_with(b"0") {
                    return None;
                }
                let numerator = String::from_utf8(numerator).unwrap();
                match self.peek_byte() {
                    Some(b'.') => {
                        self.consume_byte();
                        let mut denumerator = Vec::new();
                        while let Some(c) = self.peek_byte() {
                            if !is_digit_byte(*c) {
                                break;
                            }
                            denumerator.push(*c);
                            self.consume_byte();
                        }
                        if denumerator.is_empty() {
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
                    Err(_) => None,
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
                        Err(_) => None,
                    },
                }
            }
            // EOI or Error
            _ => None,
        }
    }
}

fn is_digit_byte(c: u8) -> bool {
    matches!(c, b'0'..=b'9')
}

pub(crate) fn is_symbol_byte(c: u8) -> bool {
    is_digit_byte(c) || is_non_digit_symbol_byte(c)
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
