# This script generates the raw output of a solver for a list of benchmarks

import os
import sys, subprocess

solvers = ['cvc4', 'z3'] # TODO If adding a new solver, add it here

timeout = 10

if __name__=='__main__':

    # NOTE: A subset of SMT Comp 2020 benchmarks timed out after 300 seconds because CVC4 used a run
    # script which tried using the --strings-fmf option first. In order to generate useful data from
    # these runs, we subtract 300 seconds from their runtime, and run them without --strings-fmf.
    if(len(sys.argv) < 4):
        print("Usage: python3 get_solver_output.py <cvc4 | z3> <benchmark_list> <path_to_benchmarks> [--no-strings-fmf]")
        exit(1)

    if sys.argv[1] in solvers:
        solver = sys.argv[1]
    else:
        print("Currently only supporting the following solvers: " + str(solvers))
        exit(1)

    fp_in = open(sys.argv[2]) # Open list of .smt2 filepaths

    path_prefix = sys.argv[3]

    if(len(sys.argv) > 4 and sys.argv[4] == '--no-strings-fmf'):
        fmf = False
        print("Running without --strings-fmf")
    else:
        fmf = True
        print("Running with --strings-fmf")

    path = "../" + solver + "_output/raw"
    if not os.path.exists(path):
        os.makedirs(path)

    i = 0
    for l in fp_in:
        i += 1
        l = l[1:-1] # Strip off leading slash and trailing newline
        b_path = path_prefix + "/" + l
        b_name = l.replace('/', '_').strip('.smt2')

        print(str(i) + ": " + b_name)

        fp_out = open(path + '/' + solver + "_rawout_" + b_name, 'w')

        # WARNING: Using shell=True below introduces some security risks
        #          (see https://docs.python.org/3/library/subprocess.html#security-considerations)
        #          In this case it is necessary as CVC4 can't parse the cmdline options when shell=False.
        if solver == 'cvc4':
            try:
                if fmf:
                    raw_out = subprocess.run("../solvers/cvc4 --strings-exp --rewrite-divk --strings-fmf -t strings-lemma -t strings-conflict " + b_path, capture_output=True, text=True, shell=True, timeout=timeout)

                else:
                    raw_out = subprocess.run("../solvers/cvc4 --strings-exp --rewrite-divk -t strings-lemma -t strings-conflict " + b_path, capture_output=True, text=True, shell=True, timeout=timeout)

                out = raw_out.stdout.strip()

            except subprocess.TimeoutExpired as e:
                out = str(e.stdout, 'utf-8')

        # TODO Set options to enable Z3 output of lemmas
        elif solver == 'z3':
            try:
                raw_out = subprocess.run(["../solvers/z3", b_path], capture_output=True, text=True, timeout=timeout)
                out = raw_out.stdout.strip()
            except subprocess.TimeoutExpired as e:
                out = str(e.stdout, 'utf-8')

        fp_out.write(out)
        fp_out.close()


    fp_in.close()
    print("Done!")
