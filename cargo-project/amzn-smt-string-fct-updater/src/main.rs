// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use amzn_smt_string_fct_updater::*;
use std::{env, fs, io};

fn main() {
    let file_to_convert = env::args().nth(1).expect(
        "Expected command line arg specifying SMTLIB file to convert (without file extension)",
    );

    let mut file_ext = ".smtlib";
    let mut file = fs::File::open(file_to_convert.clone() + file_ext);
    if file.is_err() {
        file_ext = ".smt2";
        file = fs::File::open(file_to_convert.clone() + file_ext);
    }
    let file = file.expect("Error reading input file: did you accidentally include the file extension, or try to read a file without extension smtlib or smt2?");
    let reader = io::BufReader::new(file);
    let problem = transpiler::parse(reader);

    let output = transpiler::modernize_string_fcts(problem.unwrap());

    let output_string = output
        .iter()
        .map(|o| o.to_string())
        .collect::<Vec<String>>()
        .join("\n");

    std::fs::write(file_to_convert + "_upt" + file_ext, output_string)
        .expect("Error in printing to output file");
}
