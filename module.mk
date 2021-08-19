pwd := $(brazil.pwd)

cargo.crate.publish := amzn-smt-ir amzn-smt-ir-derive amzn-smt-eager-arithmetic amzn-smt-string-transformer amzn-smt-prediction
cargo.check.flags := "--all-features"
TEST_ARGS := "--all-features"

include $(BrazilMake.dir)/targets/cargo.mk
include $(BrazilRust-Kcov.dir)/targets/kcov.mk

# bindgen (used by z3-sys) requires clang
brazil.variables += run.runtimefarm
export CLANG_PATH := $(var.run.runtimefarm)/bin/x86_64-unknown-linux-gnu-clang
export LIBCLANG_PATH := $(var.run.runtimefarm)/clang-7.0.1/lib

# tell bindgen where to find the z3 headers
brazil.variables += [Z3Prover]run.includedirs
export BINDGEN_EXTRA_CLANG_ARGS := -I$(var.[Z3Prover]run.includedirs)
$(info BINDGEN_EXTRA_CLANG_ARGS is [${BINDGEN_EXTRA_CLANG_ARGS}])

all: test fmt-check clippy
release: kcov-brazil-coverage kcov-check-coverage

# For more build customization options, see:
# - https://code.amazon.com/packages/BrazilRust
# - https://www.gnu.org/software/make
