// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use anyhow::{bail, Context};
use std::{
    ffi::OsString,
    fs, io,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
enum Config {
    Encode(EncodeCfg),
    Solve(SolveCfg),
}

#[derive(Debug, StructOpt)]
struct EncodeCfg {
    /// SMT-LIB file to encode.
    #[structopt(parse(from_os_str))]
    instance: PathBuf,
    /// Write generated CNF encoding to a file.
    #[structopt(parse(from_os_str))]
    cnf_outfile: PathBuf,
}

#[derive(Debug, StructOpt)]
struct SolveCfg {
    /// SMT-LIB file to solve.
    #[structopt(parse(from_os_str))]
    instance: PathBuf,
    /// SAT solver to use.
    #[structopt(long, default_value = "kissat")]
    solver: OsString,
}

fn main() -> anyhow::Result<()> {
    let config = Config::from_args();

    let reader = |path: &Path| -> anyhow::Result<_> {
        let file = fs::File::open(path)
            .with_context(|| format!("Unable to open file: {}", path.display()))?;
        Ok(io::BufReader::new(file))
    };

    match config {
        Config::Encode(EncodeCfg {
            instance,
            cnf_outfile,
        }) => {
            println!("Encoding {}", instance.display());
            let problem = reader(instance.as_ref())?;
            // Spawn minisat to simplify the generated CNF. The simplified formula it generates
            // cannot be mapped back to the original variables (as far as I can tell), so models
            // for the simplified version cannot be translated back. If we need models, cadical
            // supports writing simplified output and seems to preserve the original variables.
            // It can be run as `cadical -o <OUTFILE>`.
            let mut minisat = Command::new("minisat")
                .arg("-verb=0")
                .arg(format!("-dimacs={}", cnf_outfile.to_string_lossy()))
                .stdin(Stdio::piped())
                .spawn()
                .context("Unable to spawn `minisat` for CNF simplification")?;
            amzn_smt_eager_arithmetic::encode(problem, minisat.stdin.as_mut().unwrap())?;
            let exit = minisat.wait()?;
            if exit.success() {
                Ok(())
            } else {
                bail!("minisat exited with non-success status {}", exit)
            }
        }
        Config::Solve(SolveCfg { instance, solver }) => {
            println!("Solving {}", instance.display());
            let problem = reader(instance.as_ref())?;
            match amzn_smt_eager_arithmetic::solve(problem, solver)? {
                Some(model) => println!("sat\n{}", model),
                None => println!("unsat"),
            }
            Ok(())
        }
    }
}
