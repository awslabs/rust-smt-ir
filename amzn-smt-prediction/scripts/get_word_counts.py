# This script generates a file for each benchmark corresponding to the
# number of words in each line of hte raw output. It also outputs some
# statistics as it runs to give the user an idea of the distribution of
# the counts.

import os, sys

solvers = ['cvc4', 'z3'] # TODO If adding a new solver, add it here


# For each line in the raw output of the solver,
# write the length of the line to a new file
def write_word_counts(fp_raw_out, fp_count_out):
    for l in fp_raw_out:
        num_words = len(l.split())
        fp_count_out.write(str(num_words) + '\n')


if __name__=='__main__':

    if(len(sys.argv) < 3):
        print("Usage: python3 get_word_counts.py <cvc4 | z3> <benchmark_list>")
        exit(1)

    if sys.argv[1] in solvers:
        solver = sys.argv[1]
    else:
        print("Currently only supporting the following solvers: " + str(solvers))
        exit(1)

    fp_in         = open(sys.argv[2]) # List of .smt2 filepaths
    base_path     = "../" + solver + "_output"
    path_to_read  = base_path + "/raw"
    path_to_write = base_path + "/counts"

    if not os.path.exists(path_to_write):
        os.makedirs(path_to_write)

    i = 0

    for l in fp_in:
        i += 1

        b_path = l[1:-1] # Strip off leading slash and trailing newline
        b_name = b_path.replace('/', '_').strip('.smt2')
 
        fp_raw_out   = open(path_to_read  + '/' + solver + "_rawout_" + b_name)     # Path to raw output of solver
        fp_count_out = open(path_to_write + '/' + solver + "_count_" + b_name, 'w') # Path where we will write the word counts

        write_word_counts(fp_raw_out, fp_count_out)

        fp_raw_out.close()
        fp_count_out.close()


    fp_in.close()

