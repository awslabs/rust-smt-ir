# amzn-string-transformer

This is a tool for performing homomorphic transformations on smtlib queries. 

## Installation

### Preconditions:

- Make sure you have rust set up and installed.
  [Here is a link](https://www.rust-lang.org/) to Rust information including installation instructions.
- Install a solver. This tool has been tested with
  [z3](https://github.com/Z3Prover/z3#building-z3-using-make-and-gccclang),
  [cvc4 1.7 and 1.8](http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/), and
  [cvc5](https://github.com/cvc5/cvc5/blob/master/INSTALL.rst) on Amazon cloud desktop and Mac OS.

### Setup

Clone and setup the repo as follows.

```
git clone https://github.com/awslabs/rust-smt-ir.git

cd rust-smt-ir/cargo-project/amzn-smt-string-transformer
cargo build --release --target-dir release

```

## Usage

### Converting

The main use case of this tool is to canonicalize an smtlib file. From the
`rust-smt-ir/cargo-project/amzn-smt-string-transformer` directory:

```
# general case
./release/release/amzn-smt-string-transformer --input-file <path to file to convert> --mode convert --mapping <mapping type> --use-global-map <boolean>

# specific example
./release/release/amzn-smt-string-transformer --input-file test_data/example1.smtlib --mode convert --mapping no-reconstruct --use-global-map false
```

This generates a transformed file,
`<path to file to convert, without file extension>_transformed.smtlib`. For example, running with
`test_data/example1.smtlib` generates the transformed file `test_data/example1_transformed.smtlib`.

It also generates a mapping file, `<path to file to convert, without file extension>_mapping.json`.
This file contains the following information:

- character mapping: what characters in the original query map to in the transformed query (if the
  `char-to-char` mapping option was used)
- string mapping: what string literals in the original query map to in the transformed query
- variable mapping: what constraint variables in the original query get renamed to in the
  transformed query
- list of constraint variables affected by the transformation (this is the list of variables whose
  solutions are remapped if you choose to reconstruct)
- variables failing to map: variables that use an unsupported string function. If this list is
  non-empty then the transformation will fail and the output SMTLIB file will contain an error
  message "Encountered unsupported string function: BAILING OUT".
- persistent string map: essentially an extended version of the string mapping, this has metadata
  about the substrings and string properties invovled in the transformation of each string literal.
  This is needed if the `use-global-map` option is true (in this case, mappings are reused for
  future queries, and so this extra context is required to see if a mapping is valid).

### Other usage options

There are a few other mode options for running this tool.

#### Subformulas

This tool can be used to produce a list of all the subformulas in an SMT file, with the variable names normalized. The subformula option can be called as follows, for an input file `example1.smtlib`:

```
./release/release/amzn-smt-string-transformer --input-file test_data/example1.smtlib --mode subformula 
```

This produces a file `example1_recon.json` that contains a list of all the subformulas in `example1.smtlib`, but with the variable names normalized.

Subformulas are computed as the terms in the parse tree, and "normalizing" for the variables is defined as renaming in the order of appearance. So for example, the first variable seen in a subformula will become `v0`, the second is `v1`, etc.

As a particular example:
```
Term: (str.in.re some_var (re.range "0" "9"))

Subformulas: (re.range "0" "9")
             (str.in.re v0 (re.range "0" "9"))
```
This mode is useful for users who want to compute how many subformulas are shared between SMTLIB files.

#### Reconstruction

The tool can also be used to construct a satisfying solution for the original query, given a satisfying solution for the transformed query. Note that this mode only works if the string mapping function chosen is character-to-character (specified as `--mapping char-to-char`); with the default no-reconstruct string mapping function, we can't directly build a satisfying solution for the original problem since the mapping is not injective. However with character-to-character, reversing the character map is enough to construct a satisfying solution for the original problem.

The reconstruction option can be called as follows, for an input file `example1.smtlib`:
```
./release/release/amzn-smt-string-transformer --input-file test_data/example1.smtlib --mode reconstruct 
```
Calling the reconstruction mode requires that:

 * the original file has already been converted (with character-to-character mapping)
 * a solver has been run the transformed query, and the output has been captured
 * the query is SAT with a produced model

If these conditions are met, then the reconstruction mode can be run. This parses the model output of the solver on the transformed query, and extracts the values of the string constraint variables. Then, it reverses the string mapping function to find values for these variables that will form a satisfying solution for the original problem.

It also creates a new query, named `<original query name>_recon.smtlib` that is the original query with the reconstructed string variables added as assertions. Running a solver on this allows users to verify that this reconstructed solution is indeed a satisfying solution for the original problem.

### Testing/Validation

To validate the results, run your chosen solver on the original and transformed SMTLIB files and check that they have the same SAT/UNSAT results.
Note that if they are both SAT and a model is produced, the models will not be the same (because the strings have been changed).

We performed some larger-scale validation experiments. We've included the script for running experiments over a batch of queries, and usage instructions below.

This relies on the `gnu-parallel` utility.

The experiments are performed as follows, for each query file in the list specified to be tested:

  1. Run a user-specified solver on the query and capture the output
  2. Transform the query
  3. Run the same solver on the transformed query and capture the output

Each stage of this process is timed using the linux `time` utility.

#### Running batch experiments

To run this experiment over a list of SMT files, run the following command, from the root of the repo:
```
# general case
./parallel_test_transform_list.sh <file with list of queries to test> 
                                  <solver> 
                                  <path to directory of test files> 
                                  <boolean: use global map?>
                                  [optional: <any arguments to the solver>]

# specific case (no arguments to solver)
./parallel_test_transform_list.sh filenames.txt z3 . true &

# specific case (with arguments to solver)
./parallel_test_transform_list.sh other_filenames.txt cvc4-1.7 TestDirectory/ false --lang=smtlib --strings-exp --produce-models --quiet &
```
The `&` after these commands backgrounds the process; this is optional but highly recommended, since this can take a while if you are running over many files. Note that this script uses `nohup` and so you can safely log out of a cloud desktop or server session without killing the processes.

#### Testing one query file

To run the batch experiment explained above on just one query file, users can directly use the `test_and_transform.sh` script that is dispatched in the batch experiment. The arguments are almost the same as those for the batch experiment, with the only difference being a link to a specific query file in place of a link to a file with a list of query files.
```
# general case
./test_and_transform.sh <solver> <query file to test> <boolean: use global map?> [optional: <any arguments to the solver>]

# specific case
./test_and_transform.sh cvc4-1.7 test_data/example1.smtlib true --lang=smtlib --produce-models --strings-exp --quiet
```

#### Examining the data

We've also written a python script for analyzing the results of these experiments, available as `data_processing.py` in the root of the repo. To use it, ensure you have [pandas](https://pandas.pydata.org/) and [matplotlib](https://matplotlib.org/) installed.

This script takes as an argument the directory where the experiment output files have been written. From the directory, it determines what the queries were and creates a pandas dataframe with the original and transformed queries results, runtimes, and filesizes as well as the transpiler runtime.

The recommended usage is through interactive mode. For example:
```
ipython3 -i data_processing.py TestDirectory

# or

python3 -i data_processing.py TestDirectory
```
This will drop you into the python terminal, where you can interact with the data through the dataframe `rel_results`.

Some example usages:
```
# get a general stats summary of the input dataframe
get_summary_table(rel_results)

# scatterplot of the solver runtime on the original and transformed queries, runtimes logscaled, showing the means
scatterplot_vals_per_test((rel_results.trans_solver_time, "transformed"), (rel_results.orig_solver_time, "original"),
                                 ylabel="solver runtime", yunits="(s)", logscale=True, showmeans=True)
```
There are other common usages in comments in the script itself.
