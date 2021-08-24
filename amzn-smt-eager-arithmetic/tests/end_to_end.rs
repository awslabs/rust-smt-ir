#![cfg(feature = "varisat")]

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use amzn_smt_eager_arithmetic::solve_with_varisat;
use amzn_smt_ir::{
    logic::{all::*, arith::*},
    model::Model,
    Constant, Symbol, Term,
};
use num_traits::ToPrimitive;
use std::{fs::File, io::BufReader, path::Path};

fn solve(smt: &str) -> anyhow::Result<Option<Model<ALL>>> {
    solve_with_varisat(smt.as_bytes())
}

fn solve_file(path: impl AsRef<Path>) -> anyhow::Result<Option<Model<ALL>>> {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = manifest_dir.parent().unwrap().join("benches").join(path);
    let smt = File::open(&path)
        .unwrap_or_else(|e| panic!("Unable to open file {}: {}", path.to_string_lossy(), e));
    solve_with_varisat(BufReader::new(smt))
}

macro_rules! assert_sat {
    ($smt:expr $(,$name:ident in $range:expr)*) => {
        match solve($smt.as_ref()).unwrap() {
            None => panic!("expected SAT, got UNSAT"),
            #[allow(unused_variables)]
            Some(solution) => {
                $(
                    match solution.get_const_value(&Symbol(String::from(stringify!($name))).into()) {
                        Some(t) => {
                            let numeral = |t: &_| match t {
                                Term::Constant(c) => match c.as_ref() {
                                    Constant::Numeral(x) => Ok(x.to_isize().unwrap_or_else(|| panic!("numeral constant too large: {}", x))),
                                    c => Err(t.clone()),
                                }
                                _ => Err(t.clone()),
                            };
                            let x = match &t {
                                Term::OtherOp(op) => match op.as_ref() {
                                    Op::Arith(ArithOp::Neg(t)) => numeral(t).map(|x| -x),
                                    _ => Err(t),
                                }
                                t => numeral(t),
                            }
                            .unwrap_or_else(|t| panic!("expected numeral constant for definition of {}, got: {}", stringify!($name), t));
                            assert!($range.contains(&x), "expected {} in {:?}, got {}", stringify!($name), $range, x);
                        }
                        None => panic!("model didn't contain {}: {:?}", stringify!($name), solution),
                    }
                )*
            }
        }
    };
}

fn assert_unsat(smt: impl AsRef<str>) {
    assert!(matches!(solve(smt.as_ref()).unwrap(), None));
}

fn fmt_int(x: isize) -> String {
    if x.is_negative() {
        format!("(- {})", x.abs())
    } else {
        format!("{}", x)
    }
}

#[test]
fn basic_sat() {
    for c in -10..10 {
        let cs = fmt_int(c);
        assert_sat!(format!("(declare-const x Int) (assert (>= x {}))", cs), x in c..);
        assert_sat!(format!("(declare-const x Int) (assert (> x {}))", cs), x in (c+1)..);
        assert_sat!(format!("(declare-const x Int) (assert (<= x {}))", cs), x in ..=c);
        assert_sat!(format!("(declare-const x Int) (assert (< x {}))", cs), x in ..c);
        assert_sat!(format!("(declare-const x Int) (assert (= x {}))", cs), x in c..=c);
    }
}

#[test]
fn basic_unsat() {
    for c in -10..10 {
        assert_unsat(format!(
            "(declare-const x Int) (assert (and (>= x {}) (< x {})))",
            fmt_int(c),
            fmt_int(c - 1)
        ));
        assert_unsat(format!(
            "(declare-const x Int) (assert (and (> x {}) (< x {})))",
            fmt_int(c),
            fmt_int(c)
        ));
        assert_unsat(format!(
            "(declare-const x Int) (assert (and (> x {}) (<= x {})))",
            fmt_int(c),
            fmt_int(c - 1)
        ));
        assert_unsat(format!(
            "(declare-const x Int) (assert (and (= x {}) (= x {})))",
            fmt_int(c),
            fmt_int(c - 1)
        ));
    }
}

#[test]
fn two_variables() {
    assert_sat!("(declare-const x Int) (declare-const y Int) (assert (and (>= x 10) (<= y 5) (>= y 0) (= (+ x y) 17)))", x in 12.., y in 0..=5);
}

#[test]
fn mathsat() -> anyhow::Result<()> {
    let sat = ["FISCHER1-1-fair.smt2", "FISCHER2-1-fair.smt2"];
    let unsat = ["FISCHER1-2-fair.smt2", "FISCHER2-2-fair.smt2"];
    for path in sat {
        assert!(solve_file(Path::new("mathsat").join(path))?.is_some());
    }
    for path in unsat {
        assert!(matches!(solve_file(Path::new("mathsat").join(path))?, None));
    }
    Ok(())
}

#[test]
fn hash() -> anyhow::Result<()> {
    let sat = ["hash_sat_03_03.smt2", "hash_sat_03_04.smt2"];
    let unsat = ["hash_uns_03_03.smt2", "hash_uns_03_04.smt2"];
    for path in sat {
        assert!(solve_file(Path::new("Hash").join(path))?.is_some());
    }
    for path in unsat {
        assert!(matches!(solve_file(Path::new("Hash").join(path))?, None));
    }
    Ok(())
}
