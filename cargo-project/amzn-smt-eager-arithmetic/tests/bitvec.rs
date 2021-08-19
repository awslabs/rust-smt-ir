#![cfg(feature = "varisat")]

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use amzn_smt_eager_arithmetic::solve_with_varisat;
use amzn_smt_ir::{logic::all::*, model::Model};
use anyhow::anyhow;

fn solve(smt: &str) -> anyhow::Result<Option<Model<ALL>>> {
    solve_with_varisat(smt.as_bytes())
}

#[test]
fn basic() -> anyhow::Result<()> {
    let smt = "
		(declare-const x (_ BitVec 2))
		(declare-const y (_ BitVec 2))
		(assert (bvule x y))
		(check-sat)
		(get-model)
	";
    solve(smt)?.ok_or_else(|| anyhow!("should be sat"))?;
    Ok(())
}
