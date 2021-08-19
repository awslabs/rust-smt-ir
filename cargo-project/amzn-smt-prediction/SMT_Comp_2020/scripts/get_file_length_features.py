# This file takes a benchmark list as input
# and outputs a file with the number of lines
# in each benchmark file.

import sys, subprocess

if __name__=='__main__':

    if(len(sys.argv) < 2):
        print("Usage: python3 get_file_length_features.py <theory>")
        exit(1)

    theory = sys.argv[1]

    fp_in = open("../benchmarks_" + theory + ".csv")
    fp_out = open("../lines_" + theory + ".csv", 'w')

    for l in fp_in:
        path = "." + l.strip('\n')
        raw_out = subprocess.run(["wc", "-l", path], capture_output=True)

        # Takes the output from "wc -l", and grabs the line count
        out = str(raw_out.stdout, "utf-8").split()[0]

        fp_out.write(out + "\n")

    fp_in.close()
    fp_out.close()

