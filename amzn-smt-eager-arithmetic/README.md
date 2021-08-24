# amzn-smt-eager-arithmetic

`amzn-smt-eager-arithmetic` is a crate for eagerly encoding subsets of SMT-LIB to SAT.

## Encoding

The eager encoding works by determining a bound `n` on the width (in bits) of integer variables for
which it must be possible to find a solution with all integer variables representable in at most `n`
bits, if a solution exists at all (i.e. the formula is satisfiable). Given `n`, integer variables
are encoded as bit-vectors of size `n`, and arithmetic operations are encoded as arbitrary-precision
bit-vector operations. Finally, the resulting boolean formula is converted to CNF and passed to a
SAT solver. For more details, see
[the paper](reports-archive.adm.cs.cmu.edu/anon/2003/CMU-CS-03-210.pdf) upon which this technique is
based.

### Normalization

Before the bound is computed, the integer components of formulas are normalized. In particular,
integer inequality constraints are converted into the form `(+ (* a x) ...) OP b` where `OP` is one
of `<, <=, =, >=, >`, `b` is an integer constant, and each term in the summation on the
left-hand-side of the inequality is an integer constant `a` multiplied by an integer variable `x`.

**Note:** This isn't exactly true of the implementation (e.g. `(* 1 x)` would be normalized to just
`x`), but the differences do not affect the bound computation.

### Bound computation

After a formula is normalized, the solution size bound is calculated in terms of the following
parameters:

- `n`: Number of integer vars
- `m`: Number of integer constraints (applications of `<, <=, =, >=, >`)
- `a_max`: Largest (in absolute value) coefficient (i.e. `a` in instances of `(* a x)`)
- `b_max`: Largest (in absolute value) constant `b` appearing on the right-hand-side of an
  inequality
- `k`: Number of non-separation constraints

  Constraints of the form `x OP b` or `x - y OP b` where `x, y` are integer variables and `OP` is
  one of `<, <=, =, >=, >` are called _separation constraints_. This parameter counts the number of
  inequality constraints that **do not** have that form.

- `w`: Maximum constraint width (number of terms in the summation on the left-hand-side)

Then, the bound is computed as follows:

```python
if k == 0:
	bound = min(n, m) * (b_max + 1)
else:
	bound = ((a_max * w) ** k) * (n + 2) * min(n + 1, m) * (b_max + 1)

bound = ceil(log2(bound + 1) + 1)
```

These bounds are taken from
[this paper](reports-archive.adm.cs.cmu.edu/anon/2003/CMU-CS-03-210.pdf).

### CNF translation

The boolean encoding is translated to CNF using the
[Tseytin transformation](https://en.wikipedia.org/wiki/Tseytin_transformation) which keeps the
resulting CNF linear in the size of the input at the expense of generating fresh variables for each
gate it contains.

## Supported logics

This approach supports quantifier-free linear integer arithmetic `QF_LIA`, although more limited
logics like `QF_IDL` can be handled more efficiently due to tighter solution size bounds.
Additionally, uninterpreted functions (and therefore logics like `QF_UFLIA`) are supported by
applying Ackermanization, which replaces function applications with fresh variables and constraints
them appropriately to ensure functionality.

## Usage

## Prerequisites

- A current version of Rust
- A SAT solver (tested with `kissat` and `cadical`)

## Setup/Install

1. Clone this repository.
2. Navigate to the `cargo-project/amzn-smt-eager-arithmetic` directory.
3. Run `cargo build --release`.

## Running

Determine the location of your Cargo target directory (`./target` by default, although it may be
different because of your configuration or build system). The binary built in the previous section
can then be found under `<TARGET_DIR>/release/amzn-smt-eager-arithmetic`.

### Solving an SMT-LIB problem

To solve an SMT-LIB problem (i.e. `*.smt2` file), run

```shell
amzn-smt-eager-arithmetic solve <PROBLEM>
```

The result (satisfiable or unsatisfiable) along with a model will be output to stdout.

### Encoding an SMT-LIB problem to a file

To perform just the encoding step, run

```shell
amzn-smt-eager-arithmetic solve <PROBLEM> <OUTPUT>
```

This will write a CNF file in DIMACS format to the path specified by `<OUTPUT>`. This SAT problem
can then be solved by a SAT solver separately.

**Note:** In this mode of operation, it is currently not possible to reconstruct a model for the
original problem given a model produced by a SAT solver for the encoding.
