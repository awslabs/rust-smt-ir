# SMT Comp 2020 Data Collection


## Benchmarks

The benchmarks were downloaded from [StarExec](https://www.starexec.org/starexec/secure/explore/spaces.jsp?id=406432) in space ``root/SMT/SMT-LIB benchmarks/2020-04-25/non-incremental/QF_SLIA`` and were stored in ``SMT_Comp_2020/non-incremental``.

To select which benchmarks to include in training and evaluating our model, we started from the [results of the competition](https://github.com/SMT-COMP/smt-comp/tree/master/2020/results/single-query).

## Runtime Prediction

### Data Processing

After unpacking the archive, the Python script ``clean_smt_comp_results.py`` was run to select out those benchmarks which met the following constraints:
* Logic was QF_SLIA
* CVC4 took at least 30 seconds to solve

The script also excludes benchmarks in the list ``disagreements_QF_SLIA`` to exclude two sets of benchmarks: (1) those on which CVC4 and Z3 disagreed (manually collected from [here](https://smt-comp.github.io/2020/disagreements/qf-slia-single-query)) and (2) those which have quantifiers, despite the theory purporting to be quantifier-free (collected by running ``grep -rl "exists" *`` in the QF_SLIA benchmark folder). Finally, the script excludes benchmarks in the list ``excluded_SLIA`` which were excluded from the competition for various reasons. It was generated using the command ``grep "QF_SLIA" benchmark_excluded_nonincremental_2020``, and the aforementioned file was downloaded from [here](https://smt-comp.github.io/2020/selected_benchmarks/benchmark_excluded_nonincremental_2020.tar.xz).

The script generates four files: the two prefixed ``benchmarks_QF_SLIA``, contain the file paths to the selected benchmarks, and those prefixed``times_QF_SLIA`` contain the results of CVC4 on those benchmarks (it can also be easily changed to generate data for Z3).

By manual analysis of the remaining benchmarks, the following lessons were learned and decisions taken:
* CVC4 timed out on nearly all of the non-trivial benchmarks in the 2018-Kepler subdirectory. Therefore they were excluded from the main QF_SLIA dataset. They were however included in their own dataset for a separate model which predicted whether or not CVC4 would timeout on a benchmark in this set.
* Z3 timed out on nearly all of the non-trivial benchmarks in general. Hence there does not appear to be interesting predictions to be made on Z3 on this dataset.

The ``benchmarks_QF_SLIA`` files are then used by the main Rust program in this repository to generate the offline features (see the main README.md for more information).

The benchmarks are split into two groups due to the way CVC4 was configured to run in SMT Comp 2020. They used a run script which attempted to solve the benchmarks first using the command-line option ``--strings-fmf``. If the solver hadn't terminated after 300 seconds, the run script cut it off and tried again without this option. Hence any benchmarks which took more than 300 seconds were actually solved without ``--strings-fmf``. Therefore, the time for those benchmarks is reduced by 300 seconds, and when the online features are generated (see below), they are run without ``--strings-fmf``. The set of benchmarks solved with ``--strings-fmf`` are listed in ``experiments_QF_SLIA/benchmarks_QF_SLIA_30-to-300.csv`` while those which were solved without it after timeout are listed in ``experiments_QF_SLIA/benchmarks_QF_SLIA_300-to-1200.csv``.


### Feature Engineering

The script ``get_file_length_features.py`` simply generates a file with the number of lines in each benchmark file. This was used in some predictive models as a weak benchmark.

NOTE: The following three scripts MUST be run sequentially.

The script ``get_solver_output.py`` generates the raw output of a solver for a list of benchmarks. This script can be ran directly, but Bash scripts are also provided which run this script for CVC4 on the SMT Comp 2020 benchmarks: ``get_solver_output_fmf.sh`` and ``get_solver_output_no_fmf.sh``.

Next, the script ``get_word_counts.py`` generates a file for each benchmark corresponding to the number of words in each line of the raw output.

Finally, the script ``get_word_count_features.py`` generates a feature set, each of which is the number of lines with x words. For example, less than 9 words, between 10 and 100, and more than 100.


## Suggesting Solver Configuration

In addition to predicting runtime, we also used this dataset to train a model on when the option ``--strings-fmf`` should be used.

### Data Processing

We expected that the option would improve runtime on many of the benchmarks within ``experiments_QF_SLIA/benchmarks_QF_SLIA_30-to-300.csv`` as these are the ones which were solved by CVC4 using that option. We ran the script ``find_faster_fmf.sh`` (which calls ``find_faster_fmf.py``) to run CVC4 with and without ``--strings-fmf`` and stored those which were faster in ``SMT_Comp_2020/experiments_CVC4_FMF/faster_fmf.csv`` and those which were slower in ``SMT_Comp_2020/experiments_CVC4_FMF/slower_fmf.csv``. Note that we also added all of the benchmarks from ``experiments_QF_SLIA/benchmarks_QF_SLIA_300-to-1200.csv`` to ``SMT_Comp_2020/experiments_CVC4_FMF/slower_fmf.csv`` as CVC4 timed out on these benchmarks in SMT Comp 2020.

Then, the scripts ``get_solver_output_fmf_faster.sh`` and ``get_solver_output_fmf_slower.sh`` were run to call ``get_solver_output.py`` on these benchmark sets to generate the solver output on them (after which, ``get_word_counts.py`` and ``get_word_count_features.py`` were called as described above in order to generate the features for the model).

