# amzn-smt-prediction

This repository contains:

* All data processing / feature creation code for my SMT predictive models (the main Rust project & the ``scripts/`` subfolder).
* The code for training and deploying the models in Amazon SageMaker (``models/``).
* A script for generating predictions about a single SMT problem file,
handling the data processing and calling of AWS SageMaker endpoints (``scripts/generate_predictions.py``).

## The Rust Project

The Rust project herein uses a [SMT parser](https://github.com/awslabs/rust-smt-ir/tree/main/cargo-project/amzn-smt-ir)
to count the number of occurances of String predicates in SMT problem files. These are referred to
as ``offline features`` in the predictive models.

To run the Rust project, from the root of this project (amzn-smt-runtime-prediction), run ``cargo run <dataset> <path_to_benchmark_list> <name_for_output>`` where dataset is one of ``smtcomp, kepler, other``.

The dataset option tells the program where to look for the data (e.g. the SMT Comp data should be stored in ``SMT_Comp_2020/non-incremental/``) and causes it to only output the features which are non-zero in those datasets (e.g. in the Kepler dataset, only ``str_concat`` and ``len`` have examples with non-zero values).

From the output name, the program generates a file named ``off_features_<name>.csv``.

## The Scripts

There are several Python scripts in the ``scripts`` folder for preprocessing the data and generating
``online features``. For more information, see the READMEs in the ``SMT_COMP_2020`` and ``Eager_Lazy`` folders, and comments at the top of each script.

