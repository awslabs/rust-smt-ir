import os, sys
from statistics import stdev

solvers   = ['cvc4', 'z3'] # TODO If adding a new solver, add it here
theories  = ['qf_slia']    # TODO If adding a new theory, add it here

# The buckets for the features to be created
# For example, if buckets = [9, 10, 100],
# four features will be returned:
# -- Number of lines with less than 9 words
# -- Number of lines with exactly 9 words
# -- Number of lines with between 10 and 100 words
# -- Number of lines with more than 100 words
default_buckets = [7, 8, 9, 10, 20, 40, 60, 80, 100]



# Returns a CSV String with the bucket labels
def get_bucket_labels(buckets=default_buckets):
    out = "less_than_" + str(buckets[0]) + ","
    i = 1

    while i < len(buckets):

        if buckets[i] == buckets[i-1] + 1:
            out += "equal_" + str(buckets[i-1]) + ","
        else:
            out += "between_" + str(buckets[i-1]) + "_" + str(buckets[i]) + ","

        i += 1

    out += "over_" + str(buckets[i-1]) + "\n"
    return out



# Given a file pointer to a list of word counts,
# computes the feature vector based on the given buckets
def get_features(fp_count_out, buckets=default_buckets):

    # Initialize feature vector with all zeros
    features = [0 for i in range(len(default_buckets)+1)]

    for l in fp_count_out:
        num_words = int(l.strip())
        
        # Determine which bucket the count falls into
        placed = False
        for i in range(len(buckets)):
            if num_words < buckets[i]:
                features[i] += 1
                placed = True
                break
        
        # If it didn't go in one yet, it goes in the last one (greater than the highest bucket limit)
        if not placed:
            features[len(buckets)] += 1


    
    return features



if __name__=='__main__':

    if(len(sys.argv) < 4):
        print("Usage: python3 get_word_count_features.py <cvc4 | z3> <theory> <benchmark_list>")
        exit(1)

    if sys.argv[1] in solvers:
        solver = sys.argv[1]
    else:
        print("Currently only supporting the following solvers: " + str(solvers))
        exit(1)

    if sys.argv[2] in theories:
        theory = sys.argv[2]
    else:
        print("Currently only supporting the following theories: " + str(theories))

    fp_in         = open(sys.argv[3]) # List of .smt2 filepaths
    base_path     = "../" + solver + "_output"
    path_to_read  = base_path + "/counts"
    path_to_write = base_path + "/features"

    if not os.path.exists(path_to_write):
        os.makedirs(path_to_write)

    fp_out = open(path_to_write + '/' + "on_features_" + theory + "_" + solver + ".csv", 'w') # Path where we will write the features

    # Write header to output
    fp_out.write(get_bucket_labels())

    i = 0

    for l in fp_in:
        i += 1

        b_path = l[1:-1] # Strip off leading slash and trailing newline
        b_name = b_path.replace('/', '_').strip('.smt2')

        print(b_name)
 
        fp_count_out = open(path_to_read  + '/' + solver + "_count_" + b_name) # Path to list of word counts

        features = get_features(fp_count_out) # Generate feature vector
        out_list = [str(x) for x in features] # Convert to list of strings
        out_str  = ",".join(out_list) + "\n"  # Convert features to comma-delimited string

        fp_out.write(out_str)

        fp_count_out.close()


    fp_in.close()
    fp_out.close()

