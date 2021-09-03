# This script runs Z3, CVC4, and amzn-smt-eager-arithmetic on
# a set of benchmarks, returning a list of which solver was fastest
# and the encoding statistics features for the Eager v. Lazy Model.
#
# Note that it doesn't return the runtimes because it doesn't run
# them all to completion. It runs Z3 first since it is typically fastest
# on QF_IDL and QF_LIA problems, then runs the other 2 solvers until they've
# passed the current fastest time. *(It does run amzn-smt-eager-arithmetic
# for at least 5 seconds regardless in order to grab the encoding statistics).


import os
from os.path import isfile
import sys, subprocess
from time import time


from generate_predictions import parse_eager_encoding_output


max_timeout = 300 # 5 minute timeout


# Runs CVC4 on the problem at b_path and returns the runtime
# Returns None if a result is not returned before the timeout
def run_cvc4(b_path, timeout):

    start = time()

    # WARNING: Using shell=True below introduces some security risks
    #          (see https://docs.python.org/3/library/subprocess.html#security-considerations)
    #          In this case it is necessary as CVC4 can't parse the cmdline options when shell=False.
    try:
        raw_out = subprocess.run("../solvers/cvc4  " + b_path, shell=True, capture_output=True, timeout=timeout)
        elapsed = time() - start
        print(raw_out) # Print output to verify things are setup correctly. Can comment out
        return elapsed
    except subprocess.TimeoutExpired as e:
        print('CVC4 Timeout')
        return None



# Runs Z3 on the problem at b_path and returns the runtime
# Returns None if a result is not returned before the timeout
def run_z3(b_path, timeout):

    start = time()

    try:
        raw_out = subprocess.run(["../solvers/z3", b_path], capture_output=True, timeout=timeout)
        elapsed = time() - start
        print(raw_out) # Print output to verify things are setup correctly. Can comment out
        return elapsed
    except subprocess.TimeoutExpired as e:
        print('Z3 Timeout')
        return None



# Runs amzn-smt-eager-arithmetic on the problem at b_path and returns the runtime
# Returns None if a result is not returned before the timeout
def run_eager_arithmetic(b_path, timeout):

    timeout = max(timeout, 5) # Need to run at least 5 seconds to capture features from encoding

    start = time()

    try:
        raw_out = subprocess.run(["../solvers/amzn-smt-eager-arithmetic", "solve", b_path], capture_output=True, text=True, timeout=timeout)
        elapsed = time() - start
        out = raw_out.stdout.strip()
        print(raw_out) # Print output to verify things are setup correctly. Can comment out
    except subprocess.TimeoutExpired as e:
        print('EA Timeout')
        elapsed = None
        out = str(e.stdout, 'utf-8')
        print(out)

    feature_string = parse_eager_encoding_output(out, b_path)
    return elapsed, feature_string



if __name__=='__main__':

    if(len(sys.argv) < 3):
        print("Usage: python3 run_eager_v_lazy.py <benchmark_list> <path_to_benchmarks>")
        exit(1)

    # Check for solvers
    if not isfile("../solvers/cvc4") or not isfile("../solvers/z3") or not isfile("../solvers/amzn-smt-eager-arithmetic"):
        print("ERROR: In order to use this script, you must have all three solvers (CVC4, Z3, and amzn-smt-eager-arithmetic) in the solvers/ subfolder.")
        exit(1)

    fp_in = open(sys.argv[1]) # Open list of .smt2 filepaths
    path_prefix = sys.argv[2]

    fp_out1 = open("fastest_solver.csv", 'w', buffering=1)
    fp_out2 = open("features.csv", 'w', buffering=1)

    i = 0
    for l in fp_in:
        i += 1
        l = l[1:-1] # Strip off leading slash and trailing newline
        b_path = path_prefix + "/" + l

        print(str(i) + ": " + b_path)

        fastest_solver = None
        fastest_time   = max_timeout

        z3_time = run_z3(b_path, fastest_time)
        if not z3_time == None:
            fastest_time = z3_time
            fastest_solver = 'z3'
            
        cvc4_time = run_cvc4(b_path, fastest_time)
        if not cvc4_time == None and cvc4_time < fastest_time:
            fastest_time = cvc4_time
            fastest_solver = 'cvc4'

        ea_time, feature_string = run_eager_arithmetic(b_path, fastest_time)
        if not ea_time == None and ea_time < fastest_time:
            fastest_time = ea_time
            fastest_solver = 'sat'

        if not fastest_solver == None:
            fp_out1.write(fastest_solver + '\n')
        else:
            fp_out1.write('None\n')
        fp_out2.write(feature_string + '\n')


    fp_in.close()
    fp_out1.close()
    fp_out2.close()
    print("Done!")

