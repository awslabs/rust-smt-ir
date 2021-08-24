#!/bin/bash

# usage: ./test_and_transform.sh solver_name path_to_example_to_convert use_global_map_boolean [solver_option]
# usage example: ./test_and_transform.sh z3 test_data/example1.smtlib false -T:600
# usage example: ./test_and_transform.sh cvc4 test_data/example1.smt2 true --lang=smtlib --produce-models --strings-exp --quiet

solver=$1
test_path=$2
use_global_map=$3
shift;shift;shift;
solver_option=$@

file_ext="${test_path##*\.}"
test_path="${test_path%%\.*}"

# file to save timing information from running the solver on the original vs the converted code
# also save timing info about running the transformer just to have this data
output_file=${test_path}_times.out

# time and run the solver on the original problem and capture output
echo "$solver $solver_option ${test_path}.${file_ext}"  > $output_file
{ time $solver $solver_option ${test_path}.${file_ext} > ${test_path}.out ; } 2>>$output_file

echo "Done running ${solver} on ${test_path}"

# now, convert the code and run it through the solver
tool_path='./release/release/amzn-smt-string-transformer'

# if there isn't a binary yet, build it
if [ ! -f $tool_path ]; then
	cargo build --bin amzn-smt-string-transformer --release --target-dir release
fi

# convert (this autogenerates the mapping and transformed code)
echo "$tool_path convert $test_path" >> $output_file
{ time $tool_path --input-file ${test_path}.${file_ext} --mode convert --mapping no-reconstruct --use-global-map $use_global_map ; } 2>>$output_file
echo "Done converting ${test_path}"

# now, time and run the solver on the transformed code
echo "$solver $solver_option ${test_path}_transformed.${file_ext}" >> $output_file
{ time $solver $solver_option ${test_path}_transformed.${file_ext} > ${test_path}_transformed.out ; } 2>>$output_file
echo "Done running ${solver} on converted ${test_path}"

echo "Done processing ${test_path}"
