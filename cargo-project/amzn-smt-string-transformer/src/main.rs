// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::reconstruct_tools::ReconstructResult;
use amzn_smt_string_transformer::*;
use std::{fs, io, path::PathBuf};
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "transpiler_args",
    about = "Arguments for the SMTLIB transpiler"
)]
struct Opt {
    /// mode (convert, reconstruct, subformulas)
    #[structopt(long)]
    mode: String,

    /// type of mapping (char-to-char or no-reconstruct)
    #[structopt(long, required_if("mode", "convert"))]
    mapping: Option<String>,

    /// input file
    #[structopt(long, short, parse(from_os_str))]
    input_file: PathBuf,

    /// flag for whether or not to use global map
    #[structopt(long, required_if("mode", "convert"))]
    use_global_map: Option<bool>,
}

// -----------------------------------------------------------------------

fn find_subformulae(args: Opt) {
    let path = args.input_file;
    let file = fs::File::open(path.clone());
    let file = file.expect("Error reading input file");
    let reader = io::BufReader::new(file);
    let problem = transpiler::parse(reader).unwrap();

    let output = subformula_parser::find_string_subforumlas(false, problem);
    let output_json = subformula_parser::SubFormulaJson::new(&output);

    let file_name = path.file_stem().unwrap();

    if matches!(
        output_json.print_json_to_file(&[file_name.to_str().unwrap(), "_recon.json"].join("")),
        Err(_)
    ) {
        println!("Error printing subformulas to output file");
    }
}

fn convert(args: Opt) {
    let use_global_map = args.use_global_map.unwrap(); // this arg is required for "convert" mode
    let mapping_type = args.mapping.unwrap(); // also required for "convert" mode
    let path = args.input_file;
    let file = fs::File::open(path.clone());
    let file = file.expect("Error reading input file");
    let reader = io::BufReader::new(file);
    let problem = transpiler::parse(reader).unwrap();

    let (mut output, mapping_obj) = transpiler::transform_ast(
        problem,
        use_global_map,
        match mapping_type.as_str() {
            "char-to-char" => true,
            "no-reconstruct" => false,
            _ => {
                println!("Expected mapping type \"char-to-char\" or \"no-reconstruct\", received: {:?}. Proceeding with default (no-reconstruct)", mapping_type);
                false
            }
        },
    );
    // reconstruct original query shape
    output = subformula_parser::reconstruct_orig_query_shape(output);

    let mut output_string = output
        .iter()
        .map(|o| o.to_string())
        .collect::<Vec<String>>()
        .join("\n");

    // if we failed to transform some vars, bail
    if !mapping_obj.failed_transformed_constraint_vars.is_empty() {
        output_string = "Encountered unsupported string function: BAILING OUT".to_string();
    }

    let (file_name, file_ext) = (path.file_stem().unwrap(), path.extension().unwrap());
    let file_name = path.parent().unwrap().join(file_name);

    std::fs::write(
        [
            file_name.to_str().unwrap(),
            "_transformed.",
            file_ext.to_str().unwrap(),
        ]
        .join(""),
        output_string,
    )
    .expect("Error in printing to file");
    mapping_obj
        .print_json_to_file(
            &({
                if use_global_map {
                    "global"
                } else {
                    file_name.to_str().unwrap()
                }
            }
            .to_owned()
                + "_mapping.json"),
        )
        .expect("Error printing to mapping file");
}

fn reconstruct(args: Opt) {
    let path = args.input_file;
    let (file_name, file_ext) = (path.file_stem().unwrap(), path.extension().unwrap());
    let file_name = path.parent().unwrap().join(file_name);
    let recon_output = reconstruct_tools::reconstruct_and_add_assertions(
        file_name.to_str().unwrap().to_string(),
        file_ext.to_str().unwrap().to_string(),
    );
    if let Ok(recon_result) = recon_output {
        match recon_result {
            ReconstructResult::SatNoModel => {
                println!("SAT: no model");
            }
            ReconstructResult::Unsat => {
                println!("UNSAT");
            }
            ReconstructResult::Timeout => {
                println!("timeout");
            }
            ReconstructResult::Unknown => {
                println!("unknown");
            }
            ReconstructResult::SatModelBuilt => {
                println!("SAT: model reconstructed");
            }
        }
    } else {
        panic!("{:?}", recon_output);
    }
}

fn main() {
    let opt = Opt::from_args();

    match opt.mode.as_str() {
        "convert" => {
            convert(opt);
        }
        "reconstruct" => {
            reconstruct(opt);
        }
        "subformula" => {
            find_subformulae(opt);
        }
        _ => {
            panic!(
                "Expected mode \"convert\" or \"reconstruct\" or \"subformula\", received: {:?}",
                opt.mode
            );
        }
    }
}
