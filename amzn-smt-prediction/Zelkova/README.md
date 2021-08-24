# Zelkova Data Collection

## A Tale of Two Transpilers

The documentation and code herein will likely be very confusing if you are unaware that there are two distinct transpilers
which are used and referred to:

[The first](https://github.com/awslabs/rust-smt-ir/tree/main/cargo-project/amzn-smt-string-transformer) is the focus of a predictive model. The file ``z3_zelkova.csv`` contains
the result of running Z3 on a set of sanitized Zelkova examples, both in their original form, and after being transformed by
this transpiler.

[The second](https://github.com/awslabs/rust-smt-ir/tree/main/cargo-project/amzn-smt-string-fct-updater) is used to convert the Zelkova examples into the modern
SMTLIB format. This is necessary for [the parser](https://github.com/awslabs/rust-smt-ir/tree/main/cargo-project/amzn-smt-ir) to successfully parse them.


## Benchmarks

The benchmarks were downloaded from an internal Drive folder with non-public access. Reach out to the Amazon Trusted Solver team for access (anyone in ARG should be able to point you in the right direction).


## Data Processing

The Python script ``clean_zelkova_results.py`` was run to exclude three sets of benchmarks: (1) there was no check sat in the file, (2) both the original and transpiled versions timed out, and (3) both the original and transpiled versions took less than 1 second to solve.

The script generates two files, depending on which option it is called with:

with ``cvc4``, it creates``benchmarks_cvc4_zelkova.csv``, which contains the file paths to the selected benchmarks, and ``fmf_faster_zelkova.csv`` which has a 1 on line x if the benchmark on line x of ``benchmarks_cvc4_zekova.csv`` was solved faster by CVC4 with the cmd line option ``--strings-fmf`` enabled, and 0 otherwise.

similarly, with ``z3``, it creates ``benchmarks_z3_zelkova.csv`` and ``transpiled_faster_zelkova.csv`` which has a 1 on line x if the benchmark on line x of ``benchmarks_z3_zelkova.csv`` was solved faster by Z3 after being transpiled, and 0 otherwise.

Next, the script ``modernize_benchmarks.py`` (in the ``scripts/`` folder at the root) was run to convert the benchmarks into the modern SMTLIB format (e.g. changing ``str.to.re`` to ``str.to_re``). This script repeatedly calls a [transpiler](https://github.com/awslabs/rust-smt-ir/tree/main/cargo-project/amzn-smt-string-fct-updater). Follow the instructions in that repo's README to build an executable, then place it in the root of this repo.

The ``benchmarks_zelkova.csv`` files are then used by the main Rust program in this repository to generate the offline features (see the main README.md for more information).

