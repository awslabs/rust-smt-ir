# amzn-smt-string-fct-updater

This is a transpiler for updating string functions used in the Zelkova "intern friendly" benchmarks so the smtlib file is compatible with [modern SMTLIB (SMTLIB 2.6)](http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml).
This lets the queries be evaluated using the [newest version of CVC4 (CVC4 1.8)](https://cvc4.github.io/downloads.html), and with [CVC5](https://github.com/cvc5/cvc5).
The updated queries can still be evaluated with [z3](https://github.com/Z3Prover/z3#building-z3-using-make-and-gccclang).

## Functionality 

This transpiler performs the following simple function name conversions:
```
; function to convert strings to regex
str.to.re --> str.to_re

; function to check if a string fits in a regex
str.in.re --> str.in_re

; the empty string regex
re.nostr --> re.none
```

There is also a more involved transformation for the `re.loop` function: in this case the name is the same but the signature has changed.
```
; convert from normal function taking 3 arguments, to an indexed function

; general case:
(re.loop (<some regex>) num1 num2) --> ((_ re.loop num1 num2) (<some regex>))

; specific example
(re.loop (re.range "a" "z") 12 12) --> ((_ re.loop 12 12) (re.range "a" "z"))
```

## Installation

### Preconditions:
Make sure you have rust set up and installed.
[Here is a link](https://www.rust-lang.org/) to Rust information including installation instructions.

### Setup
Clone and setup the repo as follows.
```
git clone https://github.com/awslabs/rust-smt-ir

cd rust-smt-ir/cargo-project/amzn-smt-string-fct-updater
cargo build --release --target-dir release
```

## Usage 

The use case of this tool is to convert an smtlib file to use modern string functions.
From the `rust-smt-ir/cargo-project/amzn-smt-string-fct-updater` directory:
```
# general case
./release/release/amzn-smt-string-fct-updater <path to file to convert, without file extension>

# specific case
./release/release/amzn-smt-string-fct-updater example1
```

This generates a transformed file, `<path to file to convert, without file extension>_upt.smtlib`.
For example, running on `example1` generates the transformed file `example1_upt.smtlib`.


Note that if the smtlib file is already in modern format, or if it doesn't use any of the string functions converted here, that is fine -- the original code is just spit back out.

Note also that this transformation **removes all the comments and extra lines of whitespace in the file**.
This is just because comments and empty lines are ignored by the parser.
This has no effect on the query, but might affect readability.

