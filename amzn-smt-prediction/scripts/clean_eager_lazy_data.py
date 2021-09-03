# This script takes a set of results comparing the performance of
# an Eager vs. a Lazy approach to SMT solving and prepares them to
# be passed to a ML model

import sys
from math import log, ceil

# This is the timeout that was used when the 
# results were generated
TIMEOUT = 3600

theories = ['idl', 'lia']



def argmin(arr):
    return arr.index(min(arr))



# Computes the bound
# When there is only one set of parameters, the value
# computed by this function should match the value in the input
#
# If there are multiple sets of parameters, this is used to
# compute the overall bound after a "naive big encoding" has
# been computed
def compute_bound(f_dict):
    m = f_dict['constraints']
    n = f_dict['vars']
    a = f_dict['a_max']
    b = f_dict['b_max']
    k = f_dict['k']
    w = f_dict['w']

    if k == 0:
        intermediate = min(n,m) * (b + 1) + 1

    else:
        intermediate = ((a * w) ** k) * (n + 2) * min(n+1, m) * (b + 1) + 1

    return ceil(log(intermediate, 2) + 1)



def get_feature_csv(f_dict):
    m = str(f_dict['constraints'])
    n = str(f_dict['vars'])
    a = str(f_dict['a_max'])
    b = str(f_dict['b_max'])
    k = str(f_dict['k'])
    w = str(f_dict['w'])

    bound = str(f_dict['bound'])

    return n + ',' + m + ',' + a + ',' + b + ',' + k + ',' + w + ',' + bound + '\n'



# Some files have multiple parameter sets
# In this case, to compute a single "naive
# big encoding", we take the sum or max
# of the input parameters, and compute the
# bound based on those
def get_naive_big_encoding(param_sets):
    f_dict = {}

    f_dict['constraints'] = sum(p['constraints'] for p in param_sets)
    f_dict['vars']        = sum(p['vars']        for p in param_sets)
    f_dict['a_max']       = max(p['a_max']       for p in param_sets)
    f_dict['b_max']       = max(p['b_max']       for p in param_sets)
    f_dict['k']           = sum(p['k']           for p in param_sets)
    f_dict['w']           = max(p['w']           for p in param_sets)

    f_dict['bound'] = compute_bound(f_dict)
    f_dict['benchmark'] = param_sets[0]['benchmark'] 
    # All dicts in param_sets *should* have the same benchmark
    # (They are multiple parameter sets from the same file)

    return f_dict


if __name__=='__main__':

    if(len(sys.argv) < 2):
        print("Usage: python3 clean_eager_lazy_data.py <theory>")
        exit(1)

    if sys.argv[1] in theories:
        theory = sys.argv[1]
    else:
        print("Currently only supporting the following theories: " + str(theories))
        exit(1)

    path_prefix = "../Eager_Lazy/"

    fp_in_results = open(path_prefix + theory + "_results.csv")
    fp_in_params  = open(path_prefix + theory + "_params.out")

    fp_out1 = open(path_prefix + "benchmarks_"  + theory + ".csv", 'w') # List of benchmarks
    fp_out2 = open(path_prefix + "best_solver_" + theory + ".csv", 'w') # List of fastest solver on benchmarks
    fp_out3 = open(path_prefix + "features_"    + theory + ".csv", 'w') # List of features for benchmarks

    # Write headers
    fp_out1.write("benchmarks\n")
    fp_out2.write("solver\n")
    fp_out3.write("vars,constraints,a_max,b_max,k,w,bound\n")

    benchmarks = []


    # Read in header with list of solvers
    solvers = fp_in_results.readline().rstrip().split(',')[1:]

    # Parse results file, record benchmarks and fastest solver on each
    for l in fp_in_results:
        l = l.rstrip() # Strip trailing newline
        args = l.split(',')

        b     = args[0]
        times = [float(args[i]) for i in range(1,len(args))]
        best  = solvers[argmin(times)]

        benchmarks.append(b)
        fp_out1.write(b + '\n')
        fp_out2.write(best + '\n')


    # Since input files don't have benchmarks in same order,
    # store to list and alphabetize
    features = []
 
    # Read first line
    l = fp_in_params.readline().rstrip()

    # Parse parameters
    while not l == "":
        b = l.split('/')[-1] # Benchmark name is at end of line

        l = fp_in_params.readline().rstrip('\n')

        param_sets = []

        while not l == "" and not l.startswith("Encoding"):

            # Strip the word "bits" so we can cast everything
            # to ints as we read the line into a dictionary
            l = l.rstrip(' bits')

            # Convert input string to dictionary
            f_dict = dict((x.strip(), int(y.strip()))
                            for x, y in (pair.split(':')
                            for pair in l.split(', ')))

            f_dict['benchmark'] = b

            try:
                # Due to the way the bound is computed here (naively) vs.
                # actually, in a few cases the bound can be off by one.
                # For our purposes we can accept that
                assert(abs(f_dict['bound'] - compute_bound(f_dict)) <= 1)
            except AssertionError:
                print("Computed bound doesn't match input file.")
                print("Parameters: " + str(f_dict))
                print("Computed bound: " + str(compute_bound(f_dict)))
                exit(1)

            param_sets.append(f_dict)
            l = fp_in_params.readline().rstrip('\n')


        # Many files only have one set of parameters
        if len(param_sets) == 1:
            features.append(param_sets[0])
        else:
            features.append(get_naive_big_encoding(param_sets))


    # Write feature sets to file
    for b in benchmarks:
        f_dict = next((Dict for Dict in features if Dict["benchmark"] == b), None)

        if f_dict == None:
            print("ERROR: No feature set for benchmark: " + b + "\n")
            exit(1)

        fp_out3.write(get_feature_csv(f_dict))


    fp_in_results.close()
    fp_in_params.close()
    fp_out1.close()
    fp_out2.close()
    fp_out3.close()

