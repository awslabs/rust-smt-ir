# amzn-smt-prediction

This repository handles all data processing / feature creation for my work on SMT Prediction.
It also (will) include a script for generating predictions about a single SMT problem file,
handling the data processing and calling of AWS SageMaker endpoints.

The Rust project herein uses a [SMT parser](https://github.com/awslabs/rust-smt-ir/tree/main/cargo-project/amzn-smt-ir)
to count the number of occurances of String predicates in SMT problem files. These are referred to
as ``offline features`` in the predictive models.

There are several Python scripts in the ``scripts`` folder for preprocessing the data and generating
``online features``. For more information, see the READMEs in the ``SMT_COMP_2020`` and ``Zelkova`` folders.

## Known Issues

None

## Documentation

##External Resources

* The Rust language: https://www.rust-lang.org
* "The Book": https://doc.rust-lang.org/book
* The Rust API Guidelines: https://rust-lang.github.io/api-guidelines/
* Other learning resources: https://doc.rust-lang.org/learn
* Cargo documentation: https://doc.rust-lang.org/cargo
* Official package repository: https://crates.io
* Make documentation (if you really, really must do something custom in build): https://www.gnu.org/software/make
