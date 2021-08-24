# This script takes a list of benchmarks as input, runs them
# on CVC4 with and without the --strings-fmf option, and
# returns those benchmarks which run faster with --strings-fmf
# enabled

import os
import sys, subprocess
from time import time

timeout = 300
start_yellow = '\033[93m'
end_yellow   = '\033[0m'

if __name__=='__main__':

    if(len(sys.argv) < 3):
        print("Usage: python3 get_solver_output.py <benchmark_list> <path_to_benchmarks>")
        exit(1)

    fp_in = open(sys.argv[1]) # Open list of .smt2 filepaths
    path_prefix = sys.argv[2]

    # buffering=1 sets line buffering, so each line will write to
    # the file as the script runs
    fp_out1 = open("faster_fmf.csv", 'w', buffering=1)
    fp_out2 = open("slower_fmf.csv", 'w', buffering=1)
    fp_out3 = open("runtimes_fmf_exp.csv", 'w', buffering=1)

    i = 0
    for l in fp_in:
        i += 1
        l = l[1:-1] # Strip off leading slash and trailing newline
        b_path = path_prefix + "/" + l
        b_name = l.replace('/', '_').strip('.smt2')

        print(str(i) + ": " + b_name)

        # WARNING: Using shell=True below introduces some security risks
        #          (see https://docs.python.org/3/library/subprocess.html#security-considerations)
        #          In this case it is necessary as CVC4 can't parse the cmdline options when shell=False.

        try:
            start = time()
            subprocess.run("../solvers/cvc4 --strings-exp --strings-fmf " + b_path, shell=True, timeout=timeout)
            elapsed_fmf = time() - start

        except subprocess.TimeoutExpired:
            elapsed_fmf = timeout

        try:
            start = time()
            subprocess.run("../solvers/cvc4 --strings-exp  " + b_path, shell=True, timeout=timeout)
            elapsed_no_fmf = time() - start

        except subprocess.TimeoutExpired:
            elapsed_no_fmf = timeout

        print("fmf: " + str(elapsed_fmf) + " no_fmf: " + str(elapsed_no_fmf) + "\n")
        
        if(elapsed_fmf < elapsed_no_fmf):
            print(start_yellow + "FMF FASTER!" + end_yellow)
            fp_out1.write(l + '\n')
        else:
            fp_out2.write(l + '\n')

        fp_out3.write(str(elapsed_fmf) + "," + str(elapsed_no_fmf) + "\n")

    fp_in.close()
    fp_out1.close()
    fp_out2.close()
    fp_out3.close()

