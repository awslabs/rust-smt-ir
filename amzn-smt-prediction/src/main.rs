use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::io::{BufReader, BufWriter};
use std::process::exit;

use amzn_smt_ir::{
    logic::{all::Op, StringOp, ALL},
    visit::{ControlFlow, SuperVisit, Visitor},
    IOp, Script, Term,
};

#[derive(Default, Debug)]
pub struct StringCounter {
    str_concat: u64,
    len: u64,
    lex_ord: u64,
    to_re: u64,
    in_re: u64,
    re_none: u64,
    re_all: u64,
    re_all_char: u64,
    re_concat: u64,
    re_union: u64,
    re_intersect: u64,
    re_kleene_star: u64,
    ref_clos_lex_ord: u64,
    sing_str_at: u64,
    substr: u64,
    prefix_of: u64,
    suffix_of: u64,
    contains: u64,
    index_of: u64,
    replace: u64,
    replace_all: u64,
    replace_re: u64,
    replace_re_all: u64,
    re_compl: u64,
    re_diff: u64,
    re_kleene_cross: u64,
    re_opt: u64,
    re_range: u64,
    re_pow: u64,
    re_loop: u64,
    is_digit: u64,
    to_code: u64,
    from_code: u64,
    to_int: u64,
    from_int: u64,
}

impl Visitor<ALL> for StringCounter {
    type BreakTy = ();

    fn visit_theory_op(&mut self, op: &IOp<ALL>) -> ControlFlow<Self::BreakTy> {
        match op.as_ref() {
            Op::String(StringOp::StrConcat(..)) => self.str_concat += 1,
            Op::String(StringOp::Len(..)) => self.len += 1,
            Op::String(StringOp::LexOrd(..)) => self.lex_ord += 1,
            Op::String(StringOp::ToRe(..)) => self.to_re += 1,
            Op::String(StringOp::InRe(..)) => self.in_re += 1,
            Op::String(StringOp::ReNone) => self.re_none += 1,
            Op::String(StringOp::ReAll) => self.re_all += 1,
            Op::String(StringOp::ReAllChar) => self.re_all_char += 1,
            Op::String(StringOp::ReConcat(..)) => self.re_concat += 1,
            Op::String(StringOp::ReUnion(..)) => self.re_union += 1,
            Op::String(StringOp::ReIntersect(..)) => self.re_intersect += 1,
            Op::String(StringOp::ReKleeneStar(..)) => self.re_kleene_star += 1,
            Op::String(StringOp::RefClosLexOrd(..)) => self.ref_clos_lex_ord += 1,
            Op::String(StringOp::SingStrAt(..)) => self.sing_str_at += 1,
            Op::String(StringOp::Substr(..)) => self.substr += 1,
            Op::String(StringOp::PrefixOf(..)) => self.prefix_of += 1,
            Op::String(StringOp::SuffixOf(..)) => self.suffix_of += 1,
            Op::String(StringOp::Contains(..)) => self.contains += 1,
            Op::String(StringOp::IndexOf(..)) => self.index_of += 1,
            Op::String(StringOp::Replace(..)) => self.replace += 1,
            Op::String(StringOp::ReplaceAll(..)) => self.replace_all += 1,
            Op::String(StringOp::ReplaceRe(..)) => self.replace_re += 1,
            Op::String(StringOp::ReplaceReAll(..)) => self.replace_re_all += 1,
            Op::String(StringOp::ReCompl(..)) => self.re_compl += 1,
            Op::String(StringOp::ReDiff(..)) => self.re_diff += 1,
            Op::String(StringOp::ReKleeneCross(..)) => self.re_kleene_cross += 1,
            Op::String(StringOp::ReOpt(..)) => self.re_opt += 1,
            Op::String(StringOp::ReRange(..)) => self.re_range += 1,
            Op::String(StringOp::RePow(..)) => self.re_pow += 1,
            Op::String(StringOp::ReLoop(..)) => self.re_loop += 1,
            Op::String(StringOp::IsDigit(..)) => self.is_digit += 1,
            Op::String(StringOp::ToCode(..)) => self.to_code += 1,
            Op::String(StringOp::FromCode(..)) => self.from_code += 1,
            Op::String(StringOp::ToInt(..)) => self.to_int += 1,
            Op::String(StringOp::FromInt(..)) => self.from_int += 1,
            _ => {} // Ignoring arithmetic operators for now
        }

        op.super_visit_with(self)
    }
}

// Returns a header for the CSV file based on which String predicates are observed in the various
// datasets. Defaults to all String predicates
fn string_counter_csv_header(d: &str) -> String {
    match d {
        "smtcomp" | "script" => "str_concat,len,to_re,in_re,re_concat,re_union,re_kleene_star,sing_str_at,substr,prefix_of,contains,index_of,replace,re_kleene_cross,re_range,to_int,from_int\n".to_string(),
        "kepler" => "str_concat,len\n".to_string(),
        _ => "str_concat,len,lex_ord,to_re,in_re,re_none,re_all,re_all_char,re_concat,re_union,re_intersect,re_kleene_star,ref_clos_lex_ord,sing_str_at,substr,prefix_of,suffix_of,contains,index_of,replace,replace_all,replace_re,replace_re_all,re_compl,re_diff,re_kleene_cross,re_opt,re_range,re_pow,re_loop,is_digit,to_code,from_code,to_int,from_int\n".to_string()
    }
}

// Returns a comma-separated String of values corresponding to a StringCounter
fn string_counter_csv_all(x: StringCounter) -> String {
    format!("{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}\n",
     x.str_concat, x.len, x.lex_ord, x.to_re, x.in_re, x.re_none, x.re_all, x.re_all_char, x.re_concat, x.re_union, x.re_intersect,
     x.re_kleene_star, x.ref_clos_lex_ord, x.sing_str_at, x.substr, x.prefix_of, x.suffix_of, x.contains, x.index_of, x.replace,
     x.replace_all, x.replace_re, x.replace_re_all, x.re_compl, x.re_diff, x.re_kleene_cross, x.re_opt, x.re_range, x.re_pow, x.re_loop,
     x.is_digit, x.to_code, x.from_code, x.to_int, x.from_int)
}

// The functions below were customized to only output those fields in which at least one file in
// the dataset has a non-zero value.

fn string_counter_csv_smtcomp(x: StringCounter) -> String {
    format!(
        "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}\n",
        x.str_concat,
        x.len,
        x.to_re,
        x.in_re,
        x.re_concat,
        x.re_union,
        x.re_kleene_star,
        x.sing_str_at,
        x.substr,
        x.prefix_of,
        x.contains,
        x.index_of,
        x.replace,
        x.re_kleene_cross,
        x.re_range,
        x.to_int,
        x.from_int
    )
}

fn string_counter_csv_kepler(x: StringCounter) -> String {
    format!("{},{}\n", x.str_concat, x.len)
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 4 {
        println!("Usage: amzn-smt-prediction <dataset> <path_to_benchmark_list> <name_for_output>");
        println!("Valid values of dataset: smtcomp, kepler, other");
        exit(1)
    }

    let dataset = &args[1];
    let path = &args[2];
    let out_name = &args[3];

    // Open list of benchmarks
    let b_list = File::open(path)?;
    let list_reader = BufReader::new(&b_list);

    // Open output file
    let out_file = File::create(format!("off_features_{}.csv", out_name))?;
    let mut out_writer = BufWriter::new(&out_file);

    // Write the header corresponding to the dataset
    out_writer.write_all(string_counter_csv_header(dataset).as_bytes())?;

    for line in list_reader.lines() {
        let mut file_name;

        // Prepend file path
        match dataset.as_str() {
            "smtcomp" | "kepler" => file_name = String::from("SMT_Comp_2020"),
            "script" => file_name = String::from("./"),
            "other" => {
                println!("No dataset specified. Looking for benchmarks in current directory.");
                file_name = String::from("./");
            }
            _ => {
                println!("Invalid value for dataset.");
                exit(1)
            }
        }

        file_name.push_str(&line?);

        println!("{}", file_name);

        // Open benchmark file
        let b_file = File::open(&file_name)?;
        let file_reader = BufReader::new(b_file);

        // Parse formulas
        let formulas = Script::<Term>::parse(file_reader);

        match formulas {
            Ok(script) => {
                let mut counter = StringCounter::default();

                // Count the String predicates
                assert_eq!(script.visit_asserted(&mut counter), ControlFlow::CONTINUE);

                // Write a line to the CSV file
                match dataset.as_str() {
                    "smtcomp" | "script" => {
                        out_writer.write_all(string_counter_csv_smtcomp(counter).as_bytes())?
                    }
                    "kepler" => {
                        out_writer.write_all(string_counter_csv_kepler(counter).as_bytes())?
                    }
                    "other" => out_writer.write_all(string_counter_csv_all(counter).as_bytes())?,
                    _ => {
                        println!("Invalid value for dataset.");
                        exit(1)
                    }
                }
            }
            Err(e) => {
                println!("Error on current benchmark.");
                eprintln!("{:?}", e);
                exit(1);
            }
        }
        out_writer.flush()?;
    }

    Ok(())
}
