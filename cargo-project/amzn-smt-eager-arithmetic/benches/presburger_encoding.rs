// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use amzn_smt_eager_arithmetic::solve;
use criterion::{criterion_group, criterion_main, Criterion};
use std::path::Path;

const SOLVER: &str = "kissat";

const QFLIA_FILES: &[&str] = &["mathsat/FISCHER1-1-fair.smt2"];
const QFUFLIA_FILES: &[&str] = &[];

fn bench_solve(c: &mut Criterion, path: impl AsRef<Path>) {
    let path = Path::new("../benches").join(path);
    let path_str = path.to_string_lossy();
    let smt = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("Unable to open {}: {}", path_str, e));
    c.bench_function(&path_str, |b| b.iter(|| solve(smt.as_bytes(), SOLVER)));
}

pub fn bench_qflia(c: &mut Criterion) {
    for path in QFLIA_FILES {
        bench_solve(c, path);
    }
}

pub fn bench_qfuflia(c: &mut Criterion) {
    for path in QFUFLIA_FILES {
        bench_solve(c, path);
    }
}

criterion_group!(
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = bench_qflia, bench_qfuflia
);
criterion_main!(benches);
