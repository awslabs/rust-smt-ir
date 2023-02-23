# amzn-smt-ir

`amzn-smt-ir` is a Rust library for working with SMT-LIB formulas.

## Representation

### Logics

SMT-LIB logics are represented by the `aws_smt_ir::Logic` trait, which encapsulates the type of
operations in the logic (more on this later) as well as whether quantifiers and uninterpreted
functions are allowed (corresponding to the `QF` (**Q**uantifier-**F**ree) and `UF` (including
**U**ninterpreted **F**unctions) prefixes in SMT-LIB logic names.) Logics that wish to leave out
non-`Core` operations, quantifiers, or uninterpreted functions can specify `aws_smt_ir::Void` as
the corresponding associated type -- since `Void` is uninhabitable, it will be impossible at the
type level for terms in the resulting logic to contain the corresponding components.

### Operations

_Note:_ This library calls SMT functions "operations" to avoid confusion with Rust's `Fn` traits.

SMT-LIB theory functions are represented as `enum`s. For instance, a simplified version of SMT-LIB
`Core` might look like the following:

```rust
enum CoreOp<Term> {
	Not(Term),
	And(Vec<Term>),
	Ite(Term, Term, Term),
}
```

This makes it possible to encode the distinctions between different functions at the type level e.g.
encoding that `not` is a unary function, `ite` is ternary, and `and` may take any number of
arguments (since it is annotated with `:left-assoc`).

_Note:_ Indexed functions are defined as containing an array of indices as their first tuple field
e.g. `Extract([IIndex; 2], Term)` for the bit-vector `extract` function.

Pre-defined `Logic`s and their corresponding operation types are defined in the `aws_smt_ir::logic`
module. Users can also define custom `Logic`s and operations using the provided derive macros to
implement the expected traits (see the "Derives" section).

### Terms

Terms are represented by `aws_smt_ir::Term<L: Logic>`, which represents an SMT term in logic `L`:

```rust
enum Term<T: Logic> {
    /// A constant value.
    Constant(IConst),

    /// A variable representing a value.
    Variable(IVar<T::Var>),

    /// An operation in SMT-LIB's Core theory.
    CoreOp(ICoreOp<T>),

    /// A non-Core operation.
    OtherOp(IOp<T>),

    /// An uninterpreted function.
    UF(IUF<T>),

    /// Simultaneous let-binding e.g. `(let ((x true) (y false)) (and x y))`
    Let(ILet<T>),

    /// SMT-LIB `match` expression -- not yet supported
    Match(IMatch<T>),

    /// Quantified term.
    Quantifier(IQuantifier<T>),
}
```

_Note:_ Because `Core` is implicitly included in every logic, `CoreOp`s may be present in any type
of `Term`.

The `I` prefixes of type names signal that the types are interned to prevent duplication (also
called [hash-consed](https://en.wikipedia.org/wiki/Hash_consing)). `I`-prefixed types are
essentially pointers to a unique copy of the data they correspond to stored in a lookup table with
hashes as keys. When a value of one of these types is instantiated, the corresponding table is first
checked to see if it contains the value; if it does, a pointer to the existing copy is returned; if
not, the value is stored in the table and a pointer to the new copy is returned. `I`-prefixed types
implement most of Rust's standard traits by delegating to the inner value, although `PartialEq` and
`Eq` are implemented with pointer equality (equivalent because there exists a unique copy of each
value).

## Traversals

The library provides two patterns for traversing IR nodes.

### Computing

The `Visit` family of traits (`Visitor`, `Visit`, and `SuperVisit`) provide a visitor pattern for
traversing IR nodes and building up some result (stored in a `Visitor`). See the traits' respective
docs for more details.

### Transforming

The `Fold` family of traits (`Folder`, `Fold`, and `SuperFold`) provide a pattern for transforming
IR nodes into other IR nodes. See the traits' respective docs for more details.

## Derives

The library provides three derive macros for generating trait implementations expected of types used
as operations (i.e. the `L::Op` of an `L: Logic`):

- `Operation`: implements the `Operation` trait, which determines how an operation is parsed from a
  function symbol and list of arguments, the `Iterate` trait, which allows for constructing an
  iterator of function arguments (used through the `Args` trait), as well as `Debug`, `Display`, and
  `From` implementations for converting the type to `IOp` and `Term`.
- `Visit`: implements the `SuperVisit` trait for performing the standard recursive traversal of an
  operation enum.
- `Fold`: implements the `SuperFold` trait for performing the standard recursive transformation of
  an operation enum.
