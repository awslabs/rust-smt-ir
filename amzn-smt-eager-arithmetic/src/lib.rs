//! Finite instantiation SAT encoding for Presburger arithmetic.

#![warn(rust_2018_idioms)]
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use amzn_smt_ir::{
    ackerman::ackermanize,
    cnf::{self, into_cnf, CnfTerm},
    eliminate::eliminate_lets,
    logic::{
        all::{Op, ALL},
        arith::*,
    },
    model::Model,
    Ctx, ISort, IVar, Logic, Script, Sorted, Term, UnknownSort,
};
use anyhow::{anyhow, Context};
use either::Either;
use smt2parser::{concrete::Constant, Numeral};
use std::{
    collections::HashMap,
    convert::TryFrom,
    ffi::OsStr,
    fmt,
    io::{self, Write},
    num::NonZeroU64,
    ops::Range,
    time::Instant,
};

mod canonicalize;
mod encoding;
use encoding::Encoder;
mod stats;

/// Solves a quantifier-free Presburger arithmetic SMT formula defined by `commands`.
/// ```no_run
/// # fn main() -> anyhow::Result<()> {
/// use std::{io, fs::File};
/// use either::Either;
/// use amzn_smt_ir::{Symbol, Term, Constant};
/// use amzn_smt_eager_arithmetic::solve;
/// let problem = "(declare-const x Int) (assert (>= x 5))";
/// match solve(problem.as_bytes(), "kissat")? {
///     None => panic!("problem is SAT"),
///     Some(solution) => match solution.get_const_value(&Symbol(String::from("x")).into()) {
///         Some(Term::Constant(c)) => match c.as_ref() {
///             Constant::Numeral(x) => assert!(x >= &(5u8.into())),
///             _ => panic!("expected numeral constant"),
///         }
///         _ => panic!("expected numeral constant"),
///     }
/// }
/// # Ok(())
/// # }
/// ```
pub fn solve(
    smt: impl io::BufRead,
    solver: impl AsRef<OsStr>,
) -> anyhow::Result<Option<Model<ALL>>> {
    let (cnf, mapping, encoder, reconstruct_ackermanized) = encode_inner(smt)?;
    let start = Instant::now();
    let assignment = cnf.solve_with(solver)?;
    println!("Solve time: {:?}", start.elapsed());
    reconstruct(assignment, mapping, encoder, reconstruct_ackermanized)
}

#[cfg(feature = "varisat")]
pub fn solve_with_varisat(smt: impl io::BufRead) -> anyhow::Result<Option<Model<ALL>>> {
    let (cnf, mapping, encoder, reconstruct_ackermanized) = encode_inner(smt)?;
    let start = Instant::now();
    let assignment = cnf.solve_with_varisat()?;
    println!("Solve time: {:?}", start.elapsed());
    reconstruct(assignment, mapping, encoder, reconstruct_ackermanized)
}

fn reconstruct(
    satisfying_assignment: Option<HashMap<cnf::Variable, bool>>,
    mapping: HashMap<BoolVariable, cnf::Variable>,
    encoder: Encoder,
    reconstruct_ackermanized: impl FnOnce(Model<ALL>) -> Model<ALL>,
) -> anyhow::Result<Option<Model<ALL>>> {
    let rev_map: HashMap<_, _> = mapping.into_iter().map(|(a, b)| (b, a)).collect();
    let satisfying_assignment = satisfying_assignment.map(|assignment| {
        assignment
            .into_iter()
            .filter_map(|(v, s)| rev_map.get(&v).map(|&v| (v, s)))
            .collect()
    });
    match satisfying_assignment {
        Some(assignment) => {
            let decoded = encoder.decode(&assignment);
            let mut model = Model::new();
            for (sym, val) in decoded {
                let sort = val.sort(&mut Default::default())?;
                model.define_const(sym, sort, val);
            }
            Ok(Some(reconstruct_ackermanized(model)))
        }
        None => Ok(None),
    }
}

pub fn encode(smt: impl io::BufRead, cnf_sink: impl Write) -> anyhow::Result<()> {
    let (cnf, _, _, _) = encode_inner(smt)?;
    cnf.write_dimacs(cnf_sink)
        .context("Unable to write CNF encoding to sink")
}

fn encode_inner(
    smt: impl io::BufRead,
) -> anyhow::Result<(
    CnfTerm,
    HashMap<BoolVariable, cnf::Variable>,
    Encoder,
    impl FnOnce(Model<ALL>) -> Model<ALL>,
)> {
    let start = Instant::now();
    let uflia = Script::<Term>::parse(smt)?;
    println!("Parse time: {:?}", start.elapsed());
    let start = Instant::now();
    let mut ctx = Ctx::default();
    // TODO: is it necessary to eliminate lets up-front?
    let uflia = eliminate_lets(&mut ctx, uflia)?;
    let (script, reconstruct_ackermanized_funcs) = ackermanize(&mut ctx, uflia)?;
    let (encoded, encoder) = encoding::Encoder::encode(ctx, script)?;
    let (cnf, mapping) = into_cnf(encoded)?;
    let mapping = mapping
        .into_iter()
        .filter_map(|(v, s)| match v.as_ref() {
            Variable::Bool(v) => Some((*v, s)),
            v => {
                unreachable!(
                    "no non-integer variables end up in CNF passed to SAT solver: {}",
                    v
                )
            }
        })
        .collect();
    println!(
        "CNF: {} vars, {} clauses",
        cnf.num_vars(),
        cnf.num_clauses()
    );
    println!("Encoding time: {:?}", start.elapsed());
    Ok((cnf, mapping, encoder, reconstruct_ackermanized_funcs))
}

fn int_term(t: &Term) -> Option<(&Numeral, bool)> {
    use ArithOp::*;
    use Op::*;
    match t {
        Term::Constant(c) => match c.as_ref() {
            Constant::Numeral(x) => Some((x, true)),
            _ => None,
        },
        Term::OtherOp(op) => {
            if let Arith(Neg(Term::Constant(c))) = op.as_ref() {
                if let Constant::Numeral(x) = c.as_ref() {
                    return Some((x, false));
                }
            }
            None
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct BoolVariable(NonZeroU64);

impl fmt::Display for BoolVariable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<L: Logic> Sorted<L> for BoolVariable {
    fn sort(&self, _: &mut Ctx) -> Result<ISort, amzn_smt_ir::UnknownSort<Term<L>>> {
        Ok(ISort::bool())
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Variable {
    Bool(BoolVariable),
    Int(IntVariable),
    Bv(IVar),
}

impl<L: Logic> Sorted<L> for Variable
where
    Self: Into<L::Var>,
{
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        match self {
            Self::Bool(..) => Ok(ISort::bool()),
            Self::Int(..) => Ok(ISort::int()),
            Self::Bv(v) => ctx
                .const_sort(v.sym())
                .cloned()
                .ok_or_else(|| UnknownSort(Term::Variable(IVar::from(self.clone().into())))),
        }
    }
}

impl Variable {
    pub fn int(&self) -> anyhow::Result<IntVariable> {
        match self {
            Variable::Int(v) => Ok(*v),
            Variable::Bool(..) => Err(anyhow!(
                "expected integer variable, got boolean variable: {}",
                self
            )),
            Variable::Bv(..) => Err(anyhow!(
                "expected integer variable, got bit-vector variable: {}",
                self
            )),
        }
    }
}

impl TryFrom<Variable> for BoolVariable {
    type Error = Variable;
    fn try_from(v: Variable) -> Result<Self, Self::Error> {
        match v {
            Variable::Bool(b) => Ok(b),
            _ => Err(v),
        }
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct IntVariable(u64);

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(v) => write!(f, "<BOOLVAR {}>", v.0),
            Self::Int(v) => write!(f, "<INTVAR {}>", v.0),
            Self::Bv(v) => write!(f, "{}", v),
        }
    }
}

impl From<BoolVariable> for Variable {
    fn from(var: BoolVariable) -> Self {
        Self::Bool(var)
    }
}

impl From<IntVariable> for Variable {
    fn from(var: IntVariable) -> Self {
        Self::Int(var)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Bit(Either<bool, BoolVariable>);

impl Bit {
    pub fn evaluate(&self, assignment: &HashMap<BoolVariable, bool>) -> Option<bool> {
        match self.0 {
            Either::Left(b) => Some(b),
            Either::Right(v) => assignment.get(&v).copied(),
        }
    }
}

impl<T: Logic> From<Bit> for Term<T>
where
    BoolVariable: Into<T::Var>,
{
    fn from(bit: Bit) -> Self {
        match bit.0 {
            Either::Left(bit) => bit.into(),
            Either::Right(var) => Term::Variable(IVar::from(var.into())),
        }
    }
}

impl From<bool> for Bit {
    fn from(b: bool) -> Self {
        Self(Either::Left(b))
    }
}

#[derive(Clone)]
struct IntVarBits(Range<u64>);

impl Iterator for IntVarBits {
    type Item = Bit;
    fn next(&mut self) -> Option<Self::Item> {
        let bit = NonZeroU64::new(self.0.next()?);
        bit.map(|bit| Bit(Either::Right(BoolVariable(bit))))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
impl DoubleEndedIterator for IntVarBits {
    fn next_back(&mut self) -> Option<Self::Item> {
        let bit = NonZeroU64::new(self.0.next_back()?);
        bit.map(|bit| Bit(Either::Right(BoolVariable(bit))))
    }
}
impl ExactSizeIterator for IntVarBits {}

#[derive(Clone)]
struct ConstantBits {
    bits: Range<usize>,
    width: usize,
    x: Numeral,
}

impl ConstantBits {
    fn new(x: Numeral) -> Self {
        let width = x.bits() as usize;
        Self {
            bits: 0..width + 1, // Add one to produce sign bit as well
            width,
            x,
        }
    }
}

impl Iterator for ConstantBits {
    type Item = Bit;
    fn next(&mut self) -> Option<Self::Item> {
        self.bits
            .next()
            .map(|bit| {
                if bit == self.width {
                    // Sign bit -- always false since `Numeral`s are unsigned
                    false
                } else {
                    self.x.bit(bit as u64)
                }
            })
            .map(|bit| Bit(Either::Left(bit)))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.bits.size_hint()
    }
}
impl DoubleEndedIterator for ConstantBits {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.bits
            .next_back()
            .map(|bit| {
                if bit == self.width {
                    // Sign bit -- always false since `Numeral`s are unsigned
                    false
                } else {
                    self.x.bit(bit as u64)
                }
            })
            .map(|bit| Bit(Either::Left(bit)))
    }
}
impl ExactSizeIterator for ConstantBits {}

#[test]
fn numeral_bits() {
    assert_eq!(ConstantBits::new(0u8.into()).len(), 1);
    assert_eq!(ConstantBits::new(1u8.into()).len(), 2);
    assert_eq!(ConstantBits::new(2u8.into()).len(), 3);
    assert_eq!(ConstantBits::new(3u8.into()).len(), 3);
}
