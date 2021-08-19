# This script takes the results of running a SMT solver on the intern-friendly
# Zelkova examples as input and outputs a list of benchmarks and a
# corresponding list of binary values, where 1 indicates that
# the transformed version of a problem was solved faster, and 0
# if the original version was solved faster.
#
# The script was used to create datasets for the following two "transformations":
# (1) using the "--strings-fmf" cmd line option
# (2) applying the amzn-smt-string-transformer

import sys

# This is the timeout that was used when the 
# results were generated
TIMEOUT = 3600

solvers = ['cvc4', 'z3'] # TODO If adding a new solver, add it here


if __name__=='__main__':

    if(len(sys.argv) < 2):
        print("Usage: python3 clean_zelkova_results.py <cvc4 | z3>")
        exit(1)

    if sys.argv[1] in solvers:
        solver = sys.argv[1]
    else:
        print("Currently only supporting the following solvers: " + str(solvers))
        exit(1)

    fp_out1 = open("benchmarks_" + solver + "_zelkova.csv", 'w')

    if solver == 'cvc4':
        try:
            fp_in = open("cvc4_zelkova.csv")
            fp_out2 = open("fmf_faster_zelkova.csv", 'w')

        except FileNotFoundError:
            print("You need the CVC4 Zelkova results.")
            exit(1)

    elif solver == 'z3':
        try:
            fp_in = open("z3_zelkova.csv")
            fp_out2 = open("transpiled_faster_zelkova.csv", 'w')

        except FileNotFoundError:
            print("You need the Z3 Zelkova results.")
            exit(1)


    fp_in.readline() # Skip header

    for l in fp_in:
        args = l.split(',')

        # 'upt' refers to the transpiled version of the benchmark file,
        # in which the input format is updated. E.g. "str.to.re" is
        # changed to "str.to_re"
        file_name = args[0] + "_upt.smtlib"

        orig_result  = args[1]
        trans_result = args[2]

        if orig_result == "gnu_timeout": orig_time = TIMEOUT
        else:                            orig_time = float(args[3])

        if trans_result == "gnu_timeout": trans_time = TIMEOUT
        else:                             trans_time = float(args[4])

        # We exclude benchmarks where
        # (1) there was no "check sat" in the file
        # (2) both the original and transpiled version times out,
        # (3) both the original and transpiled version take less than 1 second
        if not (orig_result  == "no_check_sat" or  trans_result == "no_check_sat") and \
           not (orig_result  == "gnu_timeout"  and trans_result == "gnu_timeout")  and \
           not (orig_time < 1 and trans_time < 1):

            trans_faster = 1 if trans_time < orig_time else 0
            fp_out1.write(file_name + "\n")
            fp_out2.write(str(trans_faster) + "\n")


    fp_in.close()
    fp_out1.close()
    fp_out2.close()

