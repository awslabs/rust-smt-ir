// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use aws_smt_ir::{logic::QF_LIA, Logic, QualIdentifier, Script, Term};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use smt2parser::{concrete::SyntaxBuilder, CommandStream};
use std::{fs::File, io::BufReader, path::Path, process::Command};

const QFLIA_FILES: &[&str] = &[
    "mathsat/FISCHER8-1-fair.smt2",
    "mathsat/FISCHER8-2-fair.smt2",
    "mathsat/FISCHER8-3-fair.smt2",
    "mathsat/FISCHER8-4-fair.smt2",
    "mathsat/FISCHER8-5-fair.smt2",
];

fn cvc4_parse_file(path: &str) {
    let status = Command::new("cvc4")
        .args(["--parse-only", path])
        .spawn()
        .unwrap()
        .wait()
        .unwrap();
    assert!(status.success());
}

fn bench_parse<L: Logic>(
    c: &mut Criterion,
    benches: impl IntoIterator<Item = impl AsRef<Path>>,
    logic: L,
) where
    QualIdentifier: Into<L::Var>,
{
    let mut group = c.benchmark_group(format!("parsing/{:?}", logic));
    for bench in benches {
        let path = Path::new("../benches").join(bench);
        let bench_name = path.file_name().unwrap().to_str().unwrap();
        let instance_size_bytes = std::fs::metadata(&path).unwrap().len();

        group.throughput(Throughput::Bytes(instance_size_bytes as u64));
        group.bench_with_input(
            BenchmarkId::new("amzn-smt-ir", bench_name),
            &path,
            |b, path| {
                // Don't use `iter_with_large_drop` because we include z3's teardown time as well
                b.iter(|| {
                    let f = File::open(path).unwrap();
                    let reader = BufReader::new(f);
                    black_box(Script::<Term<L>>::parse(reader).unwrap())
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new("smt2parser", bench_name),
            &path,
            |b, path| {
                b.iter(|| {
                    let f = File::open(path).unwrap();
                    let reader = BufReader::new(f);
                    black_box(
                        CommandStream::new(reader, SyntaxBuilder, None)
                            .collect::<Result<Vec<_>, _>>()
                            .unwrap(),
                    )
                })
            },
        );
        let path = path.to_str().unwrap();
        group.bench_with_input(BenchmarkId::new("cvc4", bench_name), path, |b, path| {
            b.iter(|| black_box(cvc4_parse_file(path)))
        });
    }
}

pub fn bench_qflia(c: &mut Criterion) {
    bench_parse(c, QFLIA_FILES, QF_LIA);
}

criterion_group!(benches, bench_qflia);
criterion_main!(benches);

/*
   Code removed to get rid of z3 dependencies within crate.
//    ffi::{CStr, CString},

fn z3_parse_file(path: impl AsRef<CStr>) {
    use z3_sys::*;
    unsafe {
        let cfg = Z3_mk_config();
        assert!(!cfg.is_null());

        let ctx = Z3_mk_context(cfg);
        assert_eq!(Z3_get_error_code(ctx), ErrorCode::OK);
        assert!(!ctx.is_null());

        let solver = Z3_mk_solver(ctx);
        assert_eq!(Z3_get_error_code(ctx), ErrorCode::OK);
        assert!(!solver.is_null());
        Z3_solver_inc_ref(ctx, solver);

        Z3_solver_from_file(ctx, solver, path.as_ref().as_ptr());
        assert_eq!(Z3_get_error_code(ctx), ErrorCode::OK);

        Z3_solver_dec_ref(ctx, solver);
        Z3_solver_dec_ref(ctx, solver);
        Z3_del_context(ctx);
        Z3_del_config(cfg);
    }
}

in bench_parse:
        let path = CString::new(path).unwrap();
        group.bench_with_input(BenchmarkId::new("z3", bench_name), &path, |b, path| {
            b.iter(|| black_box(z3_parse_file(path)))
        });

*/
