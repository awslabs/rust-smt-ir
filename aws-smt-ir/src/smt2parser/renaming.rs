// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

// Modifications: Copyright (c) Amazon.com, Inc. or its affiliates. All Rights Reserved.

//! Utilities for name resolution and renaming of bound symbols.

use crate::smt2parser::{
    concrete::*,
    rewriter::Rewriter,
    visitors::{Identifier, Index, Smt2Visitor, SymbolKind},
};
use num::ToPrimitive;
use std::collections::{BTreeMap, BTreeSet};

/// A [`Rewriter`] implementation that converts old-style testers `is-Foo` into a proper indexed identifier `(_ is Foo)`.
#[derive(Debug, Default)]
pub struct TesterModernizer<V>(V);

impl<V> TesterModernizer<V> {
    pub fn new(visitor: V) -> Self {
        Self(visitor)
    }
}

impl<V, Error> Rewriter for TesterModernizer<V>
where
    V: Smt2Visitor<QualIdentifier = QualIdentifier, Symbol = Symbol, Error = Error>,
{
    type V = V;
    type Error = Error;

    fn visitor(&mut self) -> &mut V {
        &mut self.0
    }

    fn visit_simple_identifier(
        &mut self,
        value: Identifier<Symbol>,
    ) -> Result<QualIdentifier, Error> {
        let value = match value {
            Identifier::Simple { symbol } if symbol.0.starts_with("is-") => {
                let is = self.0.visit_bound_symbol("is".to_string())?;
                let name = self.0.visit_bound_symbol(symbol.0[3..].to_string())?;
                Identifier::Indexed {
                    symbol: is,
                    indices: vec![Index::Symbol(name)],
                }
            }
            v => v,
        };
        self.0.visit_simple_identifier(value)
    }
}

// Amazon modification: removed config from SymbolNormalizer
// to fix a compiler warning.

/// A [`Rewriter`] implementation that normalizes local symbols into `x0`, `x1`, etc.
/// * Normalization applies to all locally resolved symbols.
/// * A different prefix is applied depending on the symbol kind (datatype, sorts,
///   functions, variables, etc).
/// * "Global" symbols (those which don't resolve locally) are ignored.
/// * Symbol names may be re-used after a `reset` or a `pop` command, but are otherwise
///   unique (disregarding the more limited lexical scoping of variables).
#[derive(Debug, Default)]
pub struct SymbolNormalizer<V> {
    /// The underlying syntax visitor.
    visitor: V,
    /// Original names of current local symbols, indexed by kind.
    current_local_symbols: BTreeMap<SymbolKind, Vec<String>>,
    /// Currently bound symbols.
    current_bound_symbols: BTreeMap<String, Vec<LocalSymbolRef>>,
    /// Encoding tables for name randomization (if any).
    encoding_tables: BTreeMap<SymbolKind, EncodingTable>,
    /// Support the scoping of symbols with `push` and `pop` commands.
    scopes: Vec<Scope>,
    /// Accumulate symbols that were not resolved (thus ignored).
    global_symbols: BTreeSet<String>,
    /// Track the maximal number of local variables simultaneously used, indexed per kind.
    max_local_symbols: BTreeMap<SymbolKind, usize>,
}

/// Reference to a local symbol.
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
struct LocalSymbolRef {
    kind: SymbolKind,
    index: usize,
}

/// Configuration for SymbolNormalizer.
#[derive(Debug, Default)]
pub struct SymbolNormalizerConfig {
    /// For each kind K and value N in the map, the first N local variables of kind K will
    /// be assigned a randomized index in the range 0..N. Other variables will be given a
    /// sequential index (greater or equal to N).
    pub randomization_space: BTreeMap<SymbolKind, usize>,
    /// Seed for the randomization of local symbols.
    pub randomization_seed: u64,
}

struct EncodingTable {
    max_size: usize,
    permutor: permutation_iterator::Permutor,
    numbers: Vec<usize>,
    indices: BTreeMap<usize, usize>,
}

impl std::fmt::Debug for EncodingTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("EncodingTable")
            .field("max_size", &self.max_size)
            .field("numbers", &self.numbers)
            .field("indices", &self.indices)
            .finish()
    }
}

impl EncodingTable {
    fn new(seed: u64, max_size: usize) -> Self {
        let permutor = permutation_iterator::Permutor::new_with_u64_key(max_size as u64, seed);
        Self {
            max_size,
            permutor,
            numbers: Vec::new(),
            indices: BTreeMap::new(),
        }
    }

    fn encode(&mut self, x: usize) -> usize {
        if x >= self.max_size {
            return x;
        }
        for _ in self.numbers.len()..=x {
            let y = self
                .permutor
                .next()
                .expect("should not be called more than max_size times")
                as usize;
            self.indices.insert(y, self.numbers.len());
            self.numbers.push(y);
        }
        self.numbers[x]
    }

    fn decode(&self, x: usize) -> usize {
        *self.indices.get(&x).unwrap_or(&x)
    }
}

/// Track the size of `current_local_symbols` and `current_bound_symbols` so that we can
/// backtrack later.
#[derive(Debug, Default)]
struct Scope {
    /// Number of local symbols index by kind.
    local: BTreeMap<SymbolKind, usize>,
    /// Current number of bound symbols.
    bound: BTreeMap<String, usize>,
}

impl<V> SymbolNormalizer<V> {
    pub fn new(visitor: V, config: SymbolNormalizerConfig) -> Self {
        let mut encoding_tables = BTreeMap::new();
        for (kind, n) in config.randomization_space.iter() {
            let table = EncodingTable::new(config.randomization_seed + *kind as u64, *n);
            encoding_tables.insert(*kind, table);
        }
        Self {
            visitor,
            // config,    Amazon change: not used
            current_local_symbols: BTreeMap::new(),
            current_bound_symbols: BTreeMap::new(),
            encoding_tables,
            global_symbols: BTreeSet::new(),
            scopes: Vec::new(),
            max_local_symbols: BTreeMap::new(),
        }
    }

    fn get_external_symbol(table: Option<&mut EncodingTable>, r: LocalSymbolRef) -> Symbol {
        use SymbolKind::*;
        let prefix = match r.kind {
            Unknown => "?",
            Variable => "x",
            Constant => "k",
            Function => "f",
            Sort => "S",
            Datatype => "T",
            TypeVar => "X",
            Constructor => "c",
            Selector => "s",
        };
        let index = match table {
            Some(table) => table.encode(r.index),
            None => r.index,
        };
        Symbol(format!("{}{}", prefix, index))
    }

    fn parse_external_symbol(&self, s: &Symbol) -> LocalSymbolRef {
        use SymbolKind::*;
        let kind = match &s.0[0..1] {
            "?" => Unknown,
            "x" => Variable,
            "k" => Constant,
            "f" => Function,
            "S" => Sort,
            "T" => Datatype,
            "X" => TypeVar,
            "c" => Constructor,
            "s" => Selector,
            _ => panic!("cannot parse symbol kind"),
        };
        let index = str::parse(&s.0[1..]).expect("cannot parse symbol index");
        let index = match self.encoding_tables.get(&kind) {
            Some(table) => table.decode(index),
            None => index,
        };
        LocalSymbolRef { kind, index }
    }

    /// Original names of the current local symbols.
    pub fn current_local_symbols(&self) -> &BTreeMap<SymbolKind, Vec<String>> {
        &self.current_local_symbols
    }

    /// Max number of the local symbols simulatenously used.
    pub fn max_local_symbols(&self) -> &BTreeMap<SymbolKind, usize> {
        &self.max_local_symbols
    }

    fn original_symbol_name(&self, r: LocalSymbolRef) -> String {
        self.current_local_symbols.get(&r.kind).unwrap()[r.index].to_string()
    }

    /// All symbol names that failed to be resolved locally at least once (e.g. theory defined symbols).
    pub fn global_symbols(&self) -> &BTreeSet<String> {
        &self.global_symbols
    }

    fn push_scope(&mut self) {
        self.scopes.push(Scope {
            local: self
                .current_local_symbols
                .iter()
                .map(|(k, v)| (*k, v.len()))
                .collect(),
            bound: self
                .current_bound_symbols
                .iter()
                .map(|(k, v)| (k.clone(), v.len()))
                .collect(),
        });
    }

    fn truncate_vectors<T: Ord, S>(sizes: &BTreeMap<T, usize>, vectors: &mut BTreeMap<T, Vec<S>>) {
        let vs = std::mem::take(vectors);
        let vs = vs
            .into_iter()
            .filter_map(|(k, mut v)| match sizes.get(&k) {
                Some(n) => {
                    v.truncate(*n);
                    Some((k, v))
                }
                None => None,
            })
            .collect();
        *vectors = vs;
    }

    fn pop_scope(&mut self) {
        if let Some(scope) = self.scopes.pop() {
            Self::truncate_vectors(&scope.local, &mut self.current_local_symbols);
            Self::truncate_vectors(&scope.bound, &mut self.current_bound_symbols);
        }
    }
}

impl<V, Error> Rewriter for SymbolNormalizer<V>
where
    V: Smt2Visitor<Symbol = Symbol, Command = Command, Error = Error>,
{
    type V = V;
    type Error = Error;

    fn visitor(&mut self) -> &mut V {
        &mut self.visitor
    }

    fn visit_push(&mut self, level: crate::smt2parser::Numeral) -> Result<Command, Error> {
        for _ in 0..level.to_usize().expect("too many levels") {
            self.push_scope();
        }
        let value = self.visitor().visit_push(level)?;
        self.process_command(value)
    }

    fn visit_pop(&mut self, level: crate::smt2parser::Numeral) -> Result<Command, Error> {
        for _ in 0..level.to_usize().expect("too many levels") {
            self.pop_scope();
        }
        let value = self.visitor().visit_pop(level)?;
        self.process_command(value)
    }

    fn visit_reset(&mut self) -> Result<Command, Error> {
        self.current_local_symbols.clear();
        self.current_bound_symbols.clear();
        self.scopes.clear();
        let value = self.visitor().visit_reset()?;
        self.process_command(value)
    }

    fn visit_bound_symbol(&mut self, value: String) -> Result<Symbol, Error> {
        let tables = &mut self.encoding_tables;
        let value = self
            .current_bound_symbols
            .get(&value)
            .map(|v| {
                let r = *v.last().unwrap();
                Self::get_external_symbol(tables.get_mut(&r.kind), r)
            })
            .unwrap_or_else(|| {
                self.global_symbols.insert(value.clone());
                Symbol(value)
            });
        self.process_symbol(value)
    }

    fn visit_fresh_symbol(&mut self, value: String, kind: SymbolKind) -> Result<Symbol, Error> {
        let r = LocalSymbolRef {
            kind,
            index: match self.current_local_symbols.get(&kind) {
                Some(v) => v.len(),
                None => 0,
            },
        };
        self.current_local_symbols
            .entry(kind)
            .or_default()
            .push(value);
        let n = self.max_local_symbols.entry(kind).or_default();
        *n = std::cmp::max(*n, r.index + 1);
        let s = Self::get_external_symbol(self.encoding_tables.get_mut(&r.kind), r);
        self.process_symbol(s)
    }

    fn bind_symbol(&mut self, symbol: &Symbol) {
        let r = self.parse_external_symbol(symbol);
        let name = self.original_symbol_name(r);
        self.current_bound_symbols.entry(name).or_default().push(r);
    }

    fn unbind_symbol(&mut self, symbol: &Symbol) {
        use std::collections::btree_map;
        let r = self.parse_external_symbol(symbol);
        let name = self.original_symbol_name(r);
        match self.current_bound_symbols.entry(name.clone()) {
            btree_map::Entry::Occupied(mut e) => {
                if let Some(scope) = self.scopes.last() {
                    if let Some(n) = scope.bound.get(&name) {
                        // Never unbind names from the previous scope.
                        assert!(e.get().len() > *n);
                    }
                }
                // Check that we unbind the expected symbol.
                assert_eq!(e.get_mut().pop().unwrap(), r);
                if e.get().is_empty() {
                    e.remove_entry();
                }
            }
            _ => panic!("invalid entry"),
        }
    }
}

#[test]
fn test_testers() {
    use crate::smt2parser::{concrete, lexer::Lexer, parser::tests::parse_tokens};

    let value = parse_tokens(Lexer::new(&b"(assert (is-Foo 3))"[..])).unwrap();
    assert!(matches!(
        value,
        Command::Assert {
            term: Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple { .. }
                },
                ..
            }
        }
    ));
    let mut builder = concrete::SyntaxBuilder;
    assert_eq!(value, value.clone().accept(&mut builder).unwrap());
    // Visit with the TesterModernizer this time.
    let mut builder = TesterModernizer::<SyntaxBuilder>::default();
    assert!(matches!(
        value.accept(&mut builder).unwrap(),
        Command::Assert {
            term: Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Indexed { .. }
                },
                ..
            }
        }
    ));
}

#[test]
fn test_declare_datatypes_renaming() {
    use crate::smt2parser::{lexer::Lexer, parser::tests::parse_tokens};

    let value = parse_tokens(Lexer::new(&b"
(declare-datatypes (
    (Type 0)
    (TypeArray 0)
)(
    ((IntType) (VectorType (typeOfVectorType Type)) (StructType (nameOfStructType Name) (typesOfStructType TypeArray)))
    ((TypeArray (valueOfTypeArray (Array Int Type)) (lengthOfTypeArray Int)))
))"[..])).unwrap();
    assert!(matches!(value, Command::DeclareDatatypes { .. }));

    let value2 = parse_tokens(Lexer::new(
        &b"
(declare-datatypes (
    (T0 0)
    (T1 0)
)(
    ((c0) (c1 (s0 T0)) (c2 (s1 Name) (s2 T1)))
    ((c3 (s3 (Array Int T0)) (s4 Int)))
))"[..],
    ))
    .unwrap();
    assert!(matches!(value2, Command::DeclareDatatypes { .. }));
    let mut builder = SyntaxBuilder;
    assert_eq!(value, value.clone().accept(&mut builder).unwrap());

    let mut builder = SymbolNormalizer::<SyntaxBuilder>::default();
    assert_eq!(value2, value.accept(&mut builder).unwrap());

    assert_eq!(
        *builder
            .max_local_symbols()
            .get(&SymbolKind::Constructor)
            .unwrap(),
        4
    );
    assert_eq!(
        *builder
            .max_local_symbols()
            .get(&SymbolKind::Selector)
            .unwrap(),
        5
    );
}

#[test]
fn test_symbol_renaming() {
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

    let mut builder = SymbolNormalizer::<SyntaxBuilder>::default();

    let command2 = command.accept(&mut builder).unwrap();
    let command3 = Command::Assert {
        term: Term::Let {
            var_bindings: vec![(
                Symbol("x0".into()),
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
                            symbol: Symbol("x0".into()),
                        },
                    }),
                    Term::Constant(Constant::Numeral(num::BigUint::from(3u32))),
                ],
            }),
        },
    };

    assert_eq!(command2, command3);
    assert_eq!(
        builder.current_local_symbols().iter().collect::<Vec<_>>(),
        vec![(&SymbolKind::Variable, &vec!["x".to_string()])]
    );
    assert_eq!(
        builder.global_symbols().iter().collect::<Vec<_>>(),
        vec!["=", "f", "x"]
    );
}

#[test]
fn test_random_renaming() {
    use crate::smt2parser::{lexer::Lexer, parser::tests::parse_tokens};

    let value = parse_tokens(Lexer::new(&b"
(declare-datatypes (
    (Type 0)
    (TypeArray 0)
)(
    ((IntType) (VectorType (typeOfVectorType Type)) (StructType (nameOfStructType Name) (typesOfStructType TypeArray)))
    ((TypeArray (valueOfTypeArray (Array Int Type)) (lengthOfTypeArray Int)))
))"[..])).unwrap();
    assert!(matches!(value, Command::DeclareDatatypes { .. }));

    let value2 = parse_tokens(Lexer::new(
        &b"
(declare-datatypes (
    (T5 0)
    (T7 0)
)(
    ((c0) (c1 (s3 T5)) (c2 (s1 Name) (s0 T7)))
    ((c3 (s2 (Array Int T5)) (s4 Int)))
))"[..],
    ))
    .unwrap();

    let mut config = SymbolNormalizerConfig::default();
    config.randomization_space.insert(SymbolKind::Selector, 4);
    config.randomization_space.insert(SymbolKind::Datatype, 12);
    config.randomization_seed = 2;

    let mut builder = SymbolNormalizer::new(SyntaxBuilder, config);
    assert_eq!(value2, value.accept(&mut builder).unwrap());

    assert_eq!(
        *builder
            .max_local_symbols()
            .get(&SymbolKind::Constructor)
            .unwrap(),
        4
    );
    assert_eq!(
        *builder
            .max_local_symbols()
            .get(&SymbolKind::Selector)
            .unwrap(),
        5
    );
}
