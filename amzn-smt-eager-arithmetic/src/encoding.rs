// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::{
    stats::StatsVisitor, BoolVariable, Constant, ConstantBits, IntVarBits, IntVariable, Term,
    Variable,
};
use crate::{canonicalize::Canonicalizer, int_term, Bit};
use amzn_smt_ir::{
    args,
    fold::{Fold, InterLogicFolder, SuperFold},
    logic::{
        all::{Op, ALL},
        ArithOp, BvOp,
    },
    try_chained,
    visit::ControlFlow,
    CoreOp, Ctx, ICoreOp, IOp, IQuantifier, ISort, ISymbol, IVar, Logic, QualIdentifier, Script,
    Sorted, UnknownSort, Void, IUF,
};
use anyhow::{anyhow, bail, Context};
use either::Either;
use itertools::Itertools;
use num_traits::{ToPrimitive, Zero};
use smt2parser::Numeral;
use std::{collections::HashMap, num::NonZeroU64};

#[derive(Clone, Copy, Default, Debug, Hash, PartialEq, Eq)]
pub struct ReducedLogic;
impl Logic for ReducedLogic {
    type Var = Variable;
    type Op = Void;
    type Quantifier = Void;
    type UninterpretedFunc = Void;
}
type Reduced = Term<ReducedLogic>;

pub struct Encoder {
    context: Ctx,
    var_bit_width_bounds: HashMap<ISymbol, u64>,
    /// Constraints implied by the boolean encoding of integers e.g. the relationship between
    /// variables representing the bits of the sum of two integers and the bits of the inputs.
    implied: Vec<Reduced>,
    next_bool_var: NonZeroU64,
    next_int_var: u64,
    var_map: HashMap<ISymbol, Variable>,
    bit_vars: HashMap<IntVariable, (BoolVariable, u64)>,
    bv_bit_vars: HashMap<IVar, (BoolVariable, u64)>,
    encoded: HashMap<BasicOp, Reduced>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
enum BasicOp {
    Plus(Reduced, Reduced),
    Minus(Reduced, Reduced),
    Gte(Reduced, Reduced),
}

impl InterLogicFolder<ALL> for Encoder {
    type U = ReducedLogic;
    type Error = anyhow::Error;

    fn context(&self) -> Option<&Ctx> {
        Some(&self.context)
    }

    fn context_mut(&mut self) -> Option<&mut Ctx> {
        Some(&mut self.context)
    }

    fn fold_var(&mut self, var: IVar<QualIdentifier>) -> Result<Term<Self::U>, Self::Error> {
        if let Some(bv) = var.to_bitvec_literal() {
            Ok(bv.into())
        } else {
            Ok(Term::from(IVar::from(self.var(&var)?)))
        }
    }

    fn fold_core_op(&mut self, op: ICoreOp<ALL>) -> Result<Term<Self::U>, Self::Error> {
        Ok(match op.super_fold_with(self)? {
            CoreOp::Eq(args) => {
                let sort = (args.first())
                    .ok_or_else(|| UnknownSort(Term::from(CoreOp::Eq(args.clone()))))?
                    .sort(&mut self.context)?;
                if sort == ISort::int() {
                    try_chained(args, |l, r| self.encode_eq(l, r))?
                } else {
                    CoreOp::Eq(args).into()
                }
            }
            op => op.into(),
        })
    }

    fn fold_theory_op(&mut self, op: IOp<ALL>) -> Result<Term<Self::U>, Self::Error> {
        use ArithOp::*;
        use BvOp::*;
        use Op::*;

        Ok(match op.as_ref() {
            Arith(Plus(args)) => (args.fold_with(self)?.into_iter().map(Ok))
                .reduce(|l, r| self.encode_plus(l?, r?))
                .transpose()?
                .unwrap_or_else(|| Constant::Numeral(0u8.into()).into()),
            Arith(Minus(args)) => (args.fold_with(self)?.into_iter().map(Ok))
                .reduce(|l, r| self.encode_minus(l?, r?))
                .transpose()?
                .unwrap_or_else(|| Constant::Numeral(0u8.into()).into()),
            Arith(Neg(arg)) => {
                let arg = arg.fold_with(self)?;
                self.encode_neg(arg)?
            }
            Arith(Gte(args)) => try_chained(args.fold_with(self)?, |l, r| self.encode_gte(l, r))?,
            Arith(Gt(args)) => try_chained(args.fold_with(self)?, |l, r| {
                self.encode_gte(r, l).map(|t| !t)
            })?,
            Arith(Lte(args)) => try_chained(args.fold_with(self)?, |l, r| self.encode_gte(r, l))?,
            BitVec(BvUle(l, r)) => {
                let (l, r) = (l, r).fold_with(self)?;
                self.encode_bvuge(r, l)?
            }
            Arith(Lt(args)) => try_chained(args.fold_with(self)?, |l, r| {
                self.encode_gte(l, r).map(|t| !t)
            })?,
            Arith(Mul(args)) => match args.as_slice() {
                [c, x] => {
                    let z = Constant::Numeral(Numeral::zero()).into();
                    if c.is_zero() {
                        z
                    } else {
                        let x = x.fold_with(self)?;
                        let (c, pos) = int_term(c)
                            .expect("canonicalization produced malformed multiplication");
                        let c = c.to_usize().unwrap();
                        let sum = (0..c).try_fold(z, |acc, _| self.encode_plus(acc, x.clone()))?;
                        if pos {
                            sum
                        } else {
                            self.encode_neg(sum)?
                        }
                    }
                }
                _ => panic!("canonicalization produced malformed multiplication"),
            },
            op => bail!("unsupported function: {}", op),
        })
    }

    fn fold_uninterpreted_func(&mut self, func: IUF<ALL>) -> Result<Term<Self::U>, Self::Error> {
        bail!(
            "Uninterpreted functions should've been eliminated by Ackermanization pass: {}",
            func
        )
    }

    fn fold_quantifier(
        &mut self,
        quantifier: IQuantifier<ALL>,
    ) -> Result<Term<Self::U>, Self::Error> {
        bail!("Quantifiers are not supported: {}", quantifier)
    }
}

macro_rules! encode_bitwise_op {
    ($encoder:expr, $l:expr, $r:expr, |$l_bits:ident, $r_bits:ident| $bitwise:expr, |$l_const:ident, $r_const:ident| $consts:expr $(,)?) => {{
        #[allow(unused_variables)]
        (|| {
            let t: Reduced = match ($l, $r) {
                (Term::Variable(l), Term::Variable(r)) => {
                    let ($l_bits, $r_bits) = ($encoder.variable_bits(l)?, $encoder.variable_bits(r)?);
                    $bitwise
                }
                (Term::Variable(x), Term::Constant(c)) => {
                    let ($l_bits, $r_bits) =
                        ($encoder.variable_bits(x)?, Encoder::constant_bits(c)?);
                    $bitwise
                },
                (Term::Constant(c), Term::Variable(x)) => {
                    let ($l_bits, $r_bits) =
                        (Encoder::constant_bits(c)?, $encoder.variable_bits(x)?);
                    $bitwise
                },
                (Term::Constant(x), Term::Constant(y)) => {
                    let ($l_const, $r_const) = (x.as_ref(), y.as_ref());
                    $consts
                }
                _ => {
                    bail!("encode_bitwise_op requires reduced terms (i.e. constants or variables)")
                }
            };
            Ok(t)
        })()
    }};
}

impl Encoder {
    /// Initializes an encoder given an upper bound on the solution size (bits per integer).
    fn new(ctx: Ctx, var_size_bounds: HashMap<ISymbol, u64>) -> Self {
        Self {
            context: ctx,
            var_bit_width_bounds: var_size_bounds,
            implied: vec![],
            next_bool_var: NonZeroU64::new(1).unwrap(),
            next_int_var: 0,
            var_map: HashMap::new(),
            bit_vars: HashMap::new(),
            bv_bit_vars: HashMap::new(),
            encoded: Default::default(),
        }
    }

    fn advance_next_bool_var(&mut self, by: u64) {
        self.next_bool_var = (self.next_bool_var.get().checked_add(by))
            .and_then(NonZeroU64::new)
            .expect("more variables than can fit in a usize");
    }

    /// Generates a new boolean variable unique to the `Encoder`.
    pub fn new_bool_var(&mut self) -> BoolVariable {
        let var = self.next_bool_var;
        self.advance_next_bool_var(1);
        BoolVariable(var)
    }

    fn new_int_var(&mut self, width: u64) -> IntVariable {
        let var = IntVariable(self.next_int_var);
        self.next_int_var += 1;
        let first_bit = BoolVariable(self.next_bool_var);
        self.advance_next_bool_var(width);
        let old = self.bit_vars.insert(var, (first_bit, width));
        debug_assert!(old.is_none(), "int variable already exists");
        var
    }

    /// Produces an iterator over a integer constant's bits, starting with the least-significant.
    fn int_const_bits(
        x: Numeral,
    ) -> impl Iterator<Item = Bit> + DoubleEndedIterator + ExactSizeIterator + Clone {
        ConstantBits::new(x)
    }

    fn constant_bits(
        c: &Constant,
    ) -> anyhow::Result<
        impl Iterator<Item = Bit> + DoubleEndedIterator + ExactSizeIterator + Clone + '_,
    > {
        match c {
            Constant::Numeral(n) => Ok(Either::Left(Self::int_const_bits(n.clone()))),
            Constant::Binary(bits) => Ok(Either::Right(bits.iter().copied().map_into())),
            Constant::Hexadecimal(_) => {
                todo!("hexadecimal bit iterator")
            }
            c => bail!("expected integer or bit-vector constant, got: {}", c),
        }
    }

    /// Produces an iterator over a integer variable's bits, starting with the least-significant.
    fn int_var_bits(
        &self,
        var: IntVariable,
    ) -> impl Iterator<Item = Bit> + DoubleEndedIterator + ExactSizeIterator + Clone {
        let (BoolVariable(start), width) = self.bit_vars[&var];
        let start = start.get();
        IntVarBits(start..start + width)
    }

    fn bit_vec_bits(
        &self,
        v: &IVar,
    ) -> impl Iterator<Item = Bit> + DoubleEndedIterator + ExactSizeIterator + Clone {
        let (BoolVariable(start), width) = self.bv_bit_vars[v];
        let start = start.get();
        IntVarBits(start..start + width)
    }

    fn variable_bits(
        &self,
        var: &Variable,
    ) -> anyhow::Result<impl Iterator<Item = Bit> + DoubleEndedIterator + ExactSizeIterator + Clone>
    {
        match var {
            Variable::Int(v) => Ok(Either::Left(self.int_var_bits(*v))),
            Variable::Bv(v) => Ok(Either::Right(self.bit_vec_bits(v))),
            v => bail!("expected integer or bit-vector variable, got: {}", v),
        }
    }

    pub fn encode(mut ctx: Ctx, script: Script<Term>) -> anyhow::Result<(Script<Reduced>, Self)> {
        let mut canonicalizer = Canonicalizer::new(&mut ctx);
        let mut script = script.try_fold(&mut canonicalizer)?;
        script.add_asserts(canonicalizer.new_asserts);
        let bounds = {
            let mut stats = StatsVisitor::new(&mut ctx);
            match script.visit_asserted(&mut stats) {
                ControlFlow::Continue(()) => (),
                ControlFlow::Break(e) => return Err(e),
            };
            stats.solution_size_upper_bound_bits()
        };
        let mut encoder = Self::new(ctx, bounds);
        let mut encoded = script.try_fold(&mut encoder)?;
        encoded.add_asserts(std::mem::take(&mut encoder.implied));
        Ok((encoded, encoder))
    }

    fn var(&mut self, var: &IVar<QualIdentifier>) -> anyhow::Result<Variable> {
        match self.var_map.get(var.sym()) {
            Some(var) => Ok(var.clone()),
            None => {
                let sort = Sorted::<ALL>::sort(var.as_ref(), &mut self.context)?;
                let new = match sort.sym_str() {
                    "Bool" => Variable::Bool(self.new_bool_var()),
                    "Int" => {
                        let bound = *self.var_bit_width_bounds.get(var.sym()).ok_or_else(|| {
                            anyhow!("unknown solution bound for constant symbol: {}", var)
                        })?;
                        Variable::Int(self.new_int_var(bound))
                    }
                    "BitVec" => {
                        if !self.bv_bit_vars.contains_key(var) {
                            let width = sort.bv_width().unwrap().to_u64().unwrap();
                            let first_bit = BoolVariable(self.next_bool_var);
                            self.advance_next_bool_var(width);
                            self.bv_bit_vars.insert(var.clone(), (first_bit, width));
                        }
                        Variable::Bv(var.clone())
                    }
                    _ => bail!("unsupported sort for {}: {}", var, sort),
                };
                self.var_map.insert(var.sym().clone(), new.clone());
                Ok(new)
            }
        }
    }

    /// Produces an iterator over the corresponding bits of two integers' bit iterators.
    /// If the integers are of different widths, the narrower one will be sign extended to
    /// match the width of the wider one.
    fn zip_bits<T: Clone + std::fmt::Debug, U: Clone + std::fmt::Debug>(
        x: impl Iterator<Item = T> + ExactSizeIterator + DoubleEndedIterator,
        y: impl Iterator<Item = U> + ExactSizeIterator + DoubleEndedIterator,
    ) -> impl Iterator<Item = (T, U)> + ExactSizeIterator + DoubleEndedIterator {
        let (mut x, mut y) = (x.rev().peekable(), y.rev().peekable());
        let (sign_x, sign_y) = (x.peek().unwrap().clone(), y.peek().unwrap().clone());
        use itertools::EitherOrBoth::*;
        (x.rev()).zip_longest(y.rev()).map(move |x| match x {
            Both(x, y) => (x, y),
            Left(x) => (x, sign_y.clone()),
            Right(y) => (sign_x.clone(), y),
        })
    }

    fn encode_plus_bitwise(
        &mut self,
        x: impl Iterator<Item = Reduced> + DoubleEndedIterator + ExactSizeIterator,
        y: impl Iterator<Item = Reduced> + DoubleEndedIterator + ExactSizeIterator,
        carry_in: Reduced,
    ) -> Reduced {
        let max_width = x.len().max(y.len()) as u64;
        // Sum could be wider than either of the arguments
        let sum_width = max_width + 1;

        // Create a variable to hold the sum of x and y
        let sum = self.new_int_var(sum_width);
        let mut sum_bits = self.int_var_bits(sum).map(Term::from);

        let (mut last_carry_in, mut msb) = (carry_in.clone(), false.into());
        let carry_out =
            Self::zip_bits(x, y)
                .zip(&mut sum_bits)
                .fold(carry_in, |carry_in, ((x, y), sum)| {
                    last_carry_in = carry_in.clone();
                    msb = sum.clone();
                    let (s, cout) = adder(x, y, carry_in);
                    self.implied.push(CoreOp::Eq([sum, s].into()).into());
                    cout
                });
        let sign_bit = sum_bits.next().unwrap();
        // If the operation overflows (carry_out_(n-1) ^ carry_in_(n-1)), we need to use
        // carry_out_(n-1) as the sign bit of the sum; otherwise, it should sign-extend the sum.
        self.implied.push(
            CoreOp::Eq(args![
                sign_bit,
                CoreOp::Ite(carry_out.clone() ^ last_carry_in, carry_out, msb).into(),
            ])
            .into(),
        );
        debug_assert!(sum_bits.next().is_none());
        Term::Variable(Variable::Int(sum).into())
    }

    fn encode_plus(&mut self, l: Reduced, r: Reduced) -> anyhow::Result<Reduced> {
        if l.is_zero() {
            return Ok(r);
        } else if r.is_zero() {
            return Ok(l);
        }

        let op = BasicOp::Plus(l.clone(), r.clone());
        let cache = &self.encoded;
        if let Some(encoded) =
            (cache.get(&op)).or_else(|| cache.get(&BasicOp::Plus(r.clone(), l.clone())))
        {
            return Ok(encoded.clone());
        }

        let encoded = encode_bitwise_op!(
            self,
            &l,
            &r,
            |l, r| self.encode_plus_bitwise(l.map_into(), r.map_into(), false.into()),
            |l, r| if let (Constant::Numeral(l), Constant::Numeral(r)) = (l, r) {
                Constant::Numeral(l + r).into()
            } else {
                bail!("non-integer constants passed to '+'")
            }
        )
        .with_context(|| format!("failed to encode op: (+ {} {})", l, r))?;

        self.encoded.insert(op, encoded.clone());
        Ok(encoded)
    }

    fn encode_neg(&mut self, x: Reduced) -> anyhow::Result<Reduced> {
        self.encode_minus(Constant::Numeral(0u8.into()).into(), x)
    }

    fn encode_minus(&mut self, l: Reduced, r: Reduced) -> anyhow::Result<Reduced> {
        // In 2's complement, a - b = a + (-b) = a + (~b + 1)
        // Negate the bits of `r` and pass in an initial carry of 1 to get subtraction from
        // `encode_plus_bitwise`
        fn minus(
            encoder: &mut Encoder,
            l: impl Iterator<Item = Reduced> + DoubleEndedIterator + ExactSizeIterator + Clone,
            r: impl Iterator<Item = Reduced> + DoubleEndedIterator + ExactSizeIterator + Clone,
        ) -> Reduced {
            let r = r.map(|bit| !bit);
            encoder.encode_plus_bitwise(l, r, true.into())
        }

        if r.is_zero() {
            return Ok(l);
        }

        let op = BasicOp::Minus(l.clone(), r.clone());
        if let Some(encoded) = self.encoded.get(&op) {
            return Ok(encoded.clone());
        }

        let encoded = encode_bitwise_op!(
            self,
            &l,
            &r,
            |x, y| minus(self, x.map_into(), y.map_into()),
            |x, y| {
                match (x, y) {
                    (Constant::Numeral(x), Constant::Numeral(y)) => {
                        if x >= y {
                            Constant::Numeral(x - y).into()
                        } else {
                            minus(
                                self,
                                Self::int_const_bits(x.clone()).map_into(),
                                Self::int_const_bits(y.clone()).map_into(),
                            )
                        }
                    }
                    _ => bail!("non-integer constants passed to '-'"),
                }
            },
        )
        .with_context(|| format!("failed to encode op: (- {} {})", l, r))?;

        self.encoded.insert(op, encoded.clone());
        Ok(encoded)
    }

    fn encode_eq(&mut self, l: Reduced, r: Reduced) -> anyhow::Result<Reduced> {
        encode_bitwise_op!(
            self,
            &l,
            &r,
            |l, r| {
                let bits_eq = Self::zip_bits(l, r)
                    .map(|(l, r)| CoreOp::Eq([l.into(), r.into()].into()).into());
                CoreOp::And(bits_eq.collect()).into()
            },
            |l, r| if let (Constant::Numeral(l), Constant::Numeral(r)) = (l, r) {
                (l == r).into()
            } else {
                bail!("non-integer constants passed to '='")
            }
        )
    }

    fn encode_gte(&mut self, l: Reduced, r: Reduced) -> anyhow::Result<Reduced> {
        let op = BasicOp::Gte(l.clone(), r.clone());
        if let Some(encoded) = self.encoded.get(&op) {
            return Ok(encoded.clone());
        }

        let encoded = encode_bitwise_op!(
            self,
            &l,
            &r,
            |x, y| {
                let mut bits =
                    Self::zip_bits(x, y).map(|(x, y)| (Reduced::from(x), Reduced::from(y)));
                let (sign_x, sign_y) = bits
                    .next_back()
                    .expect("signed integers have at least one bit");
                CoreOp::Or(args![
                    // Either x is positive (sign bit false) and y is negative (sign bit true) ...
                    !sign_x.clone() & sign_y.clone(),
                    // ... or their sign bits are the same and x >= y after stripping the sign bits
                    CoreOp::And(args![
                        CoreOp::Eq([sign_x, sign_y].into()).into(),
                        Self::encode_unsigned_gte_bitwise(bits),
                    ])
                    .into(),
                ])
                .into()
            },
            |l, r| if let (Constant::Numeral(l), Constant::Numeral(r)) = (l, r) {
                (l >= r).into()
            } else {
                bail!("non-integer constants passed to '>='")
            }
        )?;

        self.encoded.insert(op, encoded.clone());
        Ok(encoded)
    }

    fn encode_bvuge(&mut self, l: Reduced, r: Reduced) -> anyhow::Result<Reduced> {
        encode_bitwise_op!(
            self,
            &l,
            &r,
            |x, y| Self::encode_unsigned_gte_bitwise(x.map_into().zip(y.map_into())),
            |l, r| bail!("todo"),
        )
    }

    fn encode_unsigned_gte_bitwise(bits: impl Iterator<Item = (Reduced, Reduced)>) -> Reduced {
        bits.fold(None, |acc, (x, y)| {
            Some(if let Some(less_significant_bits_gte) = acc {
                CoreOp::Or(args![
                    x.clone() & !y.clone(),
                    CoreOp::And(args![
                        CoreOp::Eq([x, y].into()).into(),
                        less_significant_bits_gte
                    ])
                    .into(),
                ])
                .into()
            } else {
                x | !y
            })
        })
        .unwrap_or_else(|| true.into())
    }

    /// Reconstructs a solution to the formula encoded by `self` given a solution to its boolean encoding.
    pub fn decode(mut self, assignment: &HashMap<BoolVariable, bool>) -> HashMap<ISymbol, Term> {
        let var_map = std::mem::take(&mut self.var_map);
        var_map
            .into_iter()
            .map(|(symbol, var)| match var {
                Variable::Int(v) => {
                    let bits = self.int_var_bits(v);
                    let len = bits.len();
                    let val = bits
                        .enumerate()
                        .filter(|(_, bit)| bit.evaluate(assignment).unwrap())
                        .map(|(bit, _)| {
                            let x = 2isize.pow(bit as u32);
                            if bit == len - 1 {
                                -x
                            } else {
                                x
                            }
                        })
                        .sum::<isize>();
                    let abs = Constant::Numeral(Numeral::from(val.abs() as usize)).into();
                    let val = if val >= 0 {
                        abs
                    } else {
                        Op::Arith(ArithOp::Neg(abs)).into()
                    };
                    (symbol, val)
                }
                Variable::Bool(v) => (symbol, assignment[&v].into()),
                Variable::Bv(bv) => {
                    let bits = self
                        .bit_vec_bits(&bv)
                        .map(|bit| bit.evaluate(assignment).unwrap());
                    (bv.sym().clone(), Constant::Binary(bits.collect()).into())
                }
            })
            .collect()
    }
}

#[allow(clippy::many_single_char_names)]
fn adder(x: Reduced, y: Reduced, carry_in: Reduced) -> (Reduced, Reduced) {
    match (carry_in.const_bool(), x.const_bool(), y.const_bool()) {
        (Ok(cin), Ok(x), Ok(y)) => {
            let s = x ^ y ^ cin;
            let cout = (x && y) || (x && cin) || (y && cin);
            (s.into(), cout.into())
        }
        (Ok(x), Ok(y), Err(a)) | (Ok(x), Err(a), Ok(y)) | (Err(a), Ok(x), Ok(y)) => {
            let s = if x ^ y { !a.clone() } else { a.clone() };
            let cout = if x && y {
                true.into()
            } else if x || y {
                a.clone()
            } else {
                false.into()
            };
            (s, cout)
        }
        (Ok(x), Err(a), Err(b)) | (Err(a), Ok(x), Err(b)) | (Err(a), Err(b), Ok(x)) => {
            let s = if x {
                !(a.clone() ^ b.clone())
            } else {
                a.clone() ^ b.clone()
            };
            let cout = if x {
                a.clone() | b.clone()
            } else {
                a.clone() & b.clone()
            };
            (s, cout)
        }
        (Err(_), Err(_), Err(_)) => {
            let s = CoreOp::Xor(args![x.clone(), y.clone(), carry_in.clone()]).into();
            let cout = CoreOp::Or(args![
                x.clone() & y.clone(),
                x & carry_in.clone(),
                y & carry_in,
            ]);
            (s, cout.into())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::Bit;
    use super::*;

    const T: Bit = Bit(Either::Left(true));
    const F: Bit = Bit(Either::Left(false));

    #[test]
    fn constant_bits() {
        let bits: Vec<_> = Encoder::int_const_bits(6u8.into()).collect();
        assert_eq!(bits, vec![F, T, T, F]); // last bit is sign bit
        let reversed: Vec<_> = Encoder::int_const_bits(5u8.into()).rev().collect();
        assert_eq!(reversed, vec![F, T, F, T]); // first bit is sign bit
    }

    #[test]
    fn zip_bits_same_width() {
        let zipped = Encoder::zip_bits(
            Encoder::int_const_bits(3u8.into()),
            Encoder::int_const_bits(2u8.into()),
        );
        assert_eq!(zipped.collect::<Vec<_>>(), vec![(T, F), (T, T), (F, F)]);
        let reversed = Encoder::zip_bits(
            Encoder::int_const_bits(3u8.into()),
            Encoder::int_const_bits(2u8.into()),
        )
        .rev();
        assert_eq!(reversed.collect::<Vec<_>>(), vec![(F, F), (T, T), (T, F)]);
    }

    #[test]
    fn zip_bits_different_width() {
        let zipped = Encoder::zip_bits(
            Encoder::int_const_bits(5u8.into()),
            Encoder::int_const_bits(2u8.into()),
        );
        assert_eq!(
            zipped.collect::<Vec<_>>(),
            vec![(T, F), (F, T), (T, F), (F, F)]
        );
        let reversed = Encoder::zip_bits(
            Encoder::int_const_bits(5u8.into()),
            Encoder::int_const_bits(2u8.into()),
        )
        .rev();
        assert_eq!(
            reversed.collect::<Vec<_>>(),
            vec![(F, F), (T, F), (F, T), (T, F)]
        );
    }
}
