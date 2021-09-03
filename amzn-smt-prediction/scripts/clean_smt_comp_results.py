# This script takes the results of SMT Comp 2020 as input
# and outputs two lists of benchmarks and two corresponding
# lists of runtimes.

if __name__=='__main__':

    path_prefix = "../SMT_Comp_2020/"

    try:
        fp_in = open(path_prefix + "Job_info_orig.csv")

    except FileNotFoundError:
        print("You need to download and extract the results file.")
        exit(1)

    # We exclude benchmarks
    # (1) on which CVC4 and Z3 disagreed,
    # (2) those which were excluded in the competition (for various reasons)
    fp_disagreed_slia  = open(path_prefix + "excluded_benchmarks/disagreements_SLIA")
    fp_excluded_slia   = open(path_prefix + "excluded_benchmarks/excluded_SLIA")

    exclude_slia = []
    for line in fp_disagreed_slia:
        exclude_slia.append(line.strip('\n'))
    for line in fp_excluded_slia:
        exclude_slia.append(line.strip('\n'))

    fp_out1 = open(path_prefix + "experiments_QF_SLIA/benchmarks_QF_SLIA_30-to-300.csv", 'w')
    fp_out2 = open(path_prefix + "experiments_QF_SLIA/times_QF_SLIA_30-to-300.csv", 'w')

    fp_out3 = open(path_prefix + "experiments_QF_SLIA/benchmarks_QF_SLIA_300-to-1200.csv", 'w')
    fp_out4 = open(path_prefix + "experiments_QF_SLIA/times_QF_SLIA_300-to-1200.csv", 'w')

    fp_in.readline() # Skip header

    fp_out2.write("time\n")
    fp_out4.write("time\n")

    for l in fp_in:
        args = l.split(',')
        full_path = args[1].split('/')

        try:
            if full_path[1] == 'QF_SLIA' and (full_path[2] == '2019-full_str_int' or full_path[2] == '2019-Jiang' or full_path[4] == 'peterc-pyex-doc-cav17-z3'):
                name = "/".join(full_path[1:])                       # Reconstruct name
                full_name = "/non-incremental/" + name # Reconstruct local path to benchmark file
                solver = args[3]
                status = args[7]
                if   status == "timeout (wallclock)": wall_time = 1200
                elif status == "complete":            wall_time = float(args[9])
                else:
                    print("Encountered an unexpected status value: " + status)
                    exit(1)

                # NOTE: Can swap out with "Z3str4 SMTCOMP2020 v1.1" to get Z3 data
                if not name in exclude_slia and solver == "CVC4-sq-final":
                    if wall_time >= 30 and wall_time < 300:                    
                        fp_out1.write(full_name + "\n")
                        fp_out2.write(str(wall_time) + "\n")
                    elif wall_time >= 330:
                        fp_out3.write(full_name + "\n")
                        fp_out4.write(str(wall_time - 300) + "\n") # Drop 300 seconds from timeout of running CVC4 with --strings-fmf (see README.md)

        # Some paths won't be as deep as peterc-pyex-doc-cav17-z3
        # That's okay; if it hasn't matched yet, it isn't a benchmark
        # we're interested in
        except IndexError:
            continue

    fp_in.close()
    fp_out1.close()
    fp_out2.close()
    fp_out3.close()
    fp_out4.close()

