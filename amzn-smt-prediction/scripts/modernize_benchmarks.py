# This script takes a list of benchmarks as input and calls a transpiler
# (https://github.com/awslabs/rust-smt-ir/tree/main/amzn-smt-string-fct-updater)
# on them which converts them to the modern SMT format.
#
# NOTE: Script assumes benchmark list includes list of names with the following format:
#       name_upt.smtlib or name_upt.smt2 (as this will be the names of the generated files;
#       doing it this way allows the same benchmark list to be used for both this script and
#       the parser).
import sys, subprocess
from os.path import isfile

path_to_exec = "../../amzn-smt-string-fct-updater/release/amzn-smt-string-fct-updater"

if __name__=='__main__':

    if(len(sys.argv) < 3):
        print("Usage: python3 modernize_benchmarks.py <benchmark_list> <path_to_benchmarks>")
        exit(1)

    if not isfile(path_to_exec):
        print("ERROR: In order to use this script, you must compile a binary for 'amzn-smt-string-fct-updater' (and have it in the right place).")
        print("From the 'rust-smt-ir/amzn-smt-string-fct-updater' directory, run:")
        print("cargo build --release --target-dir .")
        exit(1)

    fp_in = open(sys.argv[1])

    for l in fp_in:
        name     = l.split('.')[0][:-4] # Get the filename, stripping off the file extension and "_upt"
        filename = sys.argv[2] + name
        raw_out  = subprocess.run([path_to_exec, filename], capture_output=True, text=True)

        print(raw_out)


    print("Done!")
    fp_in.close()

