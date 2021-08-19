# This script generates a file for each benchmark corresponding to the
# number of words in each line of hte raw output. It also outputs some
# statistics as it runs to give the user an idea of the distribution of
# the counts.

import os, sys
from statistics import stdev

solvers = ['cvc4', 'z3'] # TODO If adding a new solver, add it here

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

    for l1 in fp_in:
        i += 1

        counts   = []
        curr_min = float('inf')
        curr_max = 0

        b_path = l1[1:-1] # Strip off leading slash and trailing newline
        b_name = b_path.replace('/', '_').strip('.smt2')
 
        fp_raw_output = open(path_to_read  + '/' + solver + "_rawout_" + b_name)     # Path to output of solver
        fp_out        = open(path_to_write + '/' + solver + "_count_" + b_name, 'w') # Path where we will write the word counts

        for l2 in fp_raw_output:
            num_words = len(l2.split())

            if num_words < curr_min: curr_min = num_words
            if num_words > curr_max: curr_max = num_words

            counts.append(num_words)
            fp_out.write(str(num_words) + "\n")

        # Output stats
        # Should be useful for determining reasonable distributions for crafting model features from word counts
        print(str(i) + ": Min=" + str(curr_min) + ", Max=" + str(curr_max), ", Stdev=" + str(round(stdev(counts), 2)))

        fp_raw_output.close()
        fp_out.close()


    fp_in.close()

