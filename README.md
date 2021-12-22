## rust-smt-ir

This project provides an intermediate representation (IR) in Rust for
[SMT-LIB](http://smtlib.cs.uiowa.edu/about.shtml) queries along with
tools for performing computations over queries and transforming
queries in various ways. To demonstrate the benefit to the automated
reasoning community, the project includes two sample applications:

 1. A tool to perform homomorphic transformations on SMT-LIB queries,
 with a focus on string theory. String function applications are
 extracted into variables, and variable names are canonicalized. Most
 importantly, the string literals themselves are modified. The string
 properties that have to be maintained when transforming a string
 literal depend on the context in which this literal is used; this
 context is determined through a callgraph representation of the SMT
 query. The string properties themselves and the string functions they
 depend on are described in the
 [string_fcts](https://github.com/awslabs/rust-smt-ir/blob/main/cargo-project/amzn-smt-string-transformer/src/string_fcts.rs)
 module.  The tool and its usage is described
 [here](https://github.com/awslabs/rust-smt-ir/blob/main/cargo-project/amzn-smt-string-transformer).

 2. A tool to transform SMT-LIB queries in supported subsets of the
 language into
 [SAT](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem)
 problems.  The tool and its usage is described
 [here](https://github.com/awslabs/rust-smt-ir/blob/main/cargo-project/amzn-smt-eager-arithmetic).
 The IR is described/documented
 [here](https://github.com/awslabs/rust-smt-ir/blob/main/cargo-project/amzn-smt-ir).

 3. A tool to translate between an older "dialect" of SMT into the
 current standard. The tool and its usage are described
 [here](https://github.com/awslabs/rust-smt-ir/blob/main/cargo-project/amzn-smt-string-fct-updater).

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.

