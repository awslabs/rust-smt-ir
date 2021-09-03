import sys, configparser, json, subprocess
from os.path import isfile
from tempfile import NamedTemporaryFile
from time import time
import numpy as np

import sagemaker
from   sagemaker.predictor     import Predictor
from   sagemaker.serializers   import CSVSerializer
from   sagemaker.deserializers import CSVDeserializer

from get_solver_output       import get_cvc4_output
from get_word_counts         import write_word_counts
from get_word_count_features import get_features, get_bucket_labels
from clean_eager_lazy_data   import get_feature_csv, compute_bound, get_naive_big_encoding


# Possible outputs
outputs_runtime = ['solve quickly (30 to 60 seconds)', 'solve slowly (1 to 12 minutes)', 'timeout (over 20 minutes)']
outputs_fmf = ['do not use --strings-fmf', 'use --strings-fmf']
outputs_eager_v_lazy = ['Lazy Approach via CVC4', 'Lazy Approach via Z3', 'Eager Approach via SAT']

path_to_off_exec = "../../amzn-smt-prediction/release/amzn-smt-prediction"
path_to_ea_exec = "../../amzn-smt-eager-arithmetic/release/amzn-smt-eager-arithmetic"
ea_timeout = 5

SUPPORTED_THEORIES = ['QF_SLIA', 'QF_IDL', 'QF_LIA'] # TODO If adding a theory, add it here


start_green = '\033[92m'
end_green   = '\033[0m'


def missing_endpoint_error(theory, endpoint_name):
    print("ERROR: Config file specified the theory " + theory + " but didn't include the necessary endpoint: " + endpoint_name)



# Takes a sagemaker.predictor.Predictor and a Python list of features
# and returns a Python list of the Predictor's response
def get_prediction(predictor, features):
    raw_out = predictor.predict(features).decode('utf-8')
    return json.loads(raw_out)



# Given a feature vector, mean vector, and standard deviation vector
# (all Python lists), returns a normalized feature vector
# For features[i], means[i] is the mean of that feature, stds[i] is the stdev
def normalize_features(features, means, stds):
    normed = []
    for i in range(len(features)):
        f = features[i]
        m = means[i]
        s = stds[i]

        if s == 0:
            print("WARNING: Standard deviation is zero for feature " + str(i) + ". Returning un-normalized feature.")
            normed.append(f)
        else:
            normed.append((f-m)/s)

    return normed



# Parses the output of amzn-smt-eager-arithmetic to collect the
# statistics, returns a String in CSV form of the features 
def parse_eager_encoding_output(out, problem_file):
    param_sets = []

    # WARNING: This code is dependent on the output format of amzn-smt-eager-arithmetic.
    # As of now, there's no other way to get these stats other than parsing the output.
    # So if the output format changes, this very well could break
    for l in out.splitlines():
        if l.startswith("Partition"):
            start = l.index('{') + 2
            stop  = l.index(' bits')
            pruned = l[start:stop]
            pruned = pruned.replace(' }', '')

            f_dict = dict((x.strip(), int(y.strip()))
                            for x, y in (pair.split(':')
                            for pair in pruned.split(', ')))

            f_dict['benchmark'] = problem_file

            # Due to the way the bound is computed here (naively) vs.
            # actually, in a few cases the bound can be off by one.
            # For our purposes we can accept that
            try:
                assert(abs(f_dict['bound'] - compute_bound(f_dict)) <= 1)
            except AssertionError:
                print("Computed bound doesn't match input file.")
                print("Parameters: " + str(f_dict))
                print("Computed bound: " + str(compute_bound(f_dict)))
                exit(1)

            param_sets.append(f_dict)

    # Many files only have one set of parameters
    if len(param_sets) == 1:
        f_dict = param_sets[0]
        feature_string = get_feature_csv(f_dict).strip()
    else:
        feature_string = get_feature_csv(get_naive_big_encoding(param_sets)).strip()

    return feature_string



# Given a Python list with the values of the features
# for the Eager v. Lazy model, returns a pretty-printed String
def get_eager_lazy_feature_string(features):
    out =  "vars: " + str(features[0])
    out += ", constraints: " + str(features[1])
    out += ", a_max: " + str(features[2])
    out += ", b_max: " + str(features[3])
    out += ", k: " + str(features[4])
    out += ", w: " + str(features[5])
    out += ", bound: " + str(features[6])

    return out



# Runtime Prediction Model
# This function generates the features and queries the endpoint
# It also returns the online features it generates so that they can be passed
# to the Solver Configuration Model
def do_runtime_prediction(problem_file, endpoint_runtime):

    # Check for offline feature generation executable
    if not isfile(path_to_off_exec):
        print("ERROR: In order to use this script (as configured), you must compile a binary for 'amzn-smt-prediction' (and have it in the right place).")
        print("It is necessary to generate the features for problems of the theory type specified in config file.")
        print("From the 'rust-smt-ir/amzn-smt-prediction' directory, run:")
        print("cargo build --release --target-dir .")
        exit(1)

    # Check that the config file includes a reference to a SageMaker endpoint for the Runtime Prediction Model
    if endpoint_runtime == None:
        missing_endpoint_error("QF_SLIA", "endpoint_runtime")
        exit(1)

    # Create a temporary file to write our "benchmark list" to (just the single file we want to run predictions on)
    # And another for the offline feature generation executable to write its output to
    tmp_bench_list = NamedTemporaryFile(mode='w')

    # The offline feature generation executable expects a name for the output, with which it creates a file
    # "off_features_<name>.csv" in the current directory. We use the time so that we get a unique name each run
    tmp_output_ext = str(int(time()))
    tmp_output = "off_features_" + tmp_output_ext + ".csv"
        
    tmp_bench_list.write(problem_file)
    tmp_bench_list.flush() # Must flush since no newline


    #####  GENERATE OFFLINE FEATURES #####

    if v == 'Full': print("Generating offline features... (calling amzn-smt-prediction)")
    raw_out = subprocess.run([path_to_off_exec, "script", tmp_bench_list.name, tmp_output_ext], capture_output=True, text=True)
    out = raw_out.stdout.strip()
    if v == 'Full': print("Done.\n")

    # Get results
    with open(tmp_output) as fp:
        off_features_labels = fp.readline().strip()
        off_features_string = fp.readline().strip()

    # Clean up temporary file generated by offline feature generation executable
    subprocess.run(["rm", tmp_output])

    ##### GENERATE ONLINE FEATURES #####

    # The functions which generate the solver output and convert it into the model
    # features read and write from files. Here we use temporary files so that they
    # are automatically cleaned up when the script terminates.

    if v == 'Full': print("Generating online features... (running CVC4 for 10 seconds)")

    # Get CVC4's output on the problem
    solver_output = get_cvc4_output(problem_file, fmf=fmf)

    # Write the output to a temporaray file so the write_word_counts() function can read it in
    tmp_raw_out = NamedTemporaryFile(mode='w')
    tmp_raw_out.write(solver_output) # Write output to a temporary file
    tmp_raw_out.flush()
       
    # File pointer for word count function to read raw output from
    fp_raw_out = open(tmp_raw_out.name, 'r') 

    # Temporary file for write_word_counts() to write word counts to
    tmp_count_out = NamedTemporaryFile(mode='w', buffering=1)
    write_word_counts(fp_raw_out, tmp_count_out)

    # File pointer for get_features() to read word counts from
    fp_count_out = open(tmp_count_out.name, 'r')

    if not buckets == None:
        on_features_labels = get_bucket_labels(buckets).strip()
        on_features = get_features(fp_count_out, buckets)
    else:
        on_features_labels = get_bucket_labels().strip()
        on_features = get_features(fp_count_out)

    if v == 'Full': print("Done.")

    # Convert features to list of integers
    feature_labels = off_features_labels + ',' + on_features_labels
    features = [int(x) for x in off_features_string.split(',')] + on_features

    # Normalize features, if means and stds are provided in config
    if not feature_means1 == None and not feature_stds1 == None:
        features = normalize_features(features, feature_means1, feature_stds1)

    if v == 'Full': print("Feature Labels: " + feature_labels)
    if v == 'Full': print("Feature Vector: " + str(features) + "\n")


    ##### GENERATE INFERENCE #####

    # Create a Predictor object which references the endpoint in AWS SageMaker
    predictor = Predictor(endpoint_runtime, serializer=CSVSerializer())
    # Call the endpoint to get a prediction for our example
    prediction = get_prediction(predictor, features)

    confidence = round(max(prediction) * 100, 2)
    runtime    = outputs_runtime[np.argmax(prediction)]

    if v == 'Full': print("Possible Outputs: "+ str(outputs_runtime))
    if v == 'Full': print("Probabilities: " + str(prediction) + "\n")

    fmf_status = "ENABLED" if fmf else "DISABLED"
    if v == 'Full' or v == 'Pretty': 
        print(start_green + "The Runtime Model predicted -- with " + str(confidence) + "% confidence -- that as configured (--strings-fmf " + fmf_status +  "), CVC4 will: " + runtime + end_green)
    elif v == 'Vector':
        print(prediction)

    return on_features



# Solver Configuration Model
def do_solver_configuration(theory, endpoint_fmf, on_features):

    # Check that the config file includes a reference to a SageMaker endpoint for the Solver Configuration Model
    if endpoint_fmf == None:
        missing_endpoint_error(theory, "endpoint_fmf")
        exit(1)

    # Already generated the features for this model (the online features from the Runtime Prediction Model above)
    # So we can skip right to calling the predictor

    ##### GENERATE INFERENCE #####

    # Create a Predictor object which references the endpoint in AWS SageMaker
    predictor = Predictor(endpoint_fmf, serializer=CSVSerializer())
    # Call the endpoint to get a prediction for our example
    prediction = get_prediction(predictor, on_features) # This model only uses the online features

    confidence = round(prediction * 100, 2)

    if v == 'Full' or v == 'Pretty':
        if confidence <= 50:
            print(start_green + "But, the Solver Configuration Model predicted -- with " + str(100 - confidence) + "% confidence -- that CVC4 will find a solution faster with --strings-fmf DISABLED." + end_green)
        else:
            print(start_green + "Additionally, the Solver Configuration Model predicted -- with " + str(confidence) + "% confidence -- that CVC4 will find a solution fastest with --strings-fmf ENABLED." + end_green)
    elif v == 'Vector':
        print(prediction)



# Eager v. Lazy Model
def do_eager_lazy(problem_file, endpoint_eager_v_lazy):

    # Check for eager-arithmetic executable
    if not isfile(path_to_ea_exec):
        print("ERROR: In order to use this script (as configured), you must compile a binary for 'amzn-smt-eager-arithmetic' (and have it in the right place).")
        print("It is necessary to generate the features for problems of the theory type specified in " + config_file)
        print("From the 'rust-smt-ir/amzn-smt-eager-arithmetic' directory, run:")
        print("cargo build --release --target-dir .")
        exit(1)

    # Check that the config file includes a reference to a SageMaker endpoint for the Eager v. Lazy Model
    if endpoint_eager_v_lazy == None:
        missing_endpoint_error(theory, "endpoint_eager_v_lazy")
        exit(1)


    ##### GENERATE FEATURES #####

    # Generate statistics for feature set
    # Cuts off after 5 seconds, after which encoding is generally done and it is on to solving, which isn't necessary here
    if v == 'Full': print("Generating features... (calling amzn-smt-eager-arithmetic)")
    try:
        raw_out = subprocess.run([path_to_ea_exec, "solve", problem_file], capture_output=True, text=True, timeout=ea_timeout)
        out = raw_out.stdout.strip()
    except subprocess.TimeoutExpired as e:
        out = str(e.stdout, 'utf-8')
    if v == 'Full': print("Done.\n")

    # Parse the output to generate the features
    feature_string = parse_eager_encoding_output(out, problem_file)
    # Convert features to list of integers
    features = [int(x) for x in feature_string.split(',')]

    if v == 'Full': print("Feature Vector: " + get_eager_lazy_feature_string(features) + "\n")


    ##### GENERATE INFERENCE #####

    # Create a Predictor object which references the endpoint in AWS SageMaker
    predictor = Predictor(endpoint_eager_v_lazy, serializer=CSVSerializer())
    # Call the endpoint to get a prediction for our example
    prediction = get_prediction(predictor, features)

    confidence = round(max(prediction) * 100, 2)
    best_solver = outputs_eager_v_lazy[np.argmax(prediction)]

    if v == 'Full': print("Possible Outputs: " + str(outputs_eager_v_lazy))
    if v == 'Full': print("Probabilities: " + str(prediction) + "\n")

    if v == 'Full' or v == 'Pretty': 
        print(start_green + "The Eager v. Lazy Model predicted -- with " + str(confidence) + "% confidence -- that the fastest method to solve this benchmark is: " + best_solver + end_green)
    elif v == 'Vector':
        print(prediction)



if __name__ == '__main__':

    if(len(sys.argv) < 3):
        print("Usage: python3 generate_predictions.py <SMTLIB File> <Config File>")
        exit(1)

    problem_file = sys.argv[1]
    config_file = sys.argv[2]

    config = configparser.ConfigParser()
    config.read(config_file)

    # Get required options

    try:
        theory = config['REQUIRED']['Theory']
        if not theory in SUPPORTED_THEORIES: raise ValueError
    except (KeyError, ValueError):
        print("Theory must be specified. Acceptable values are: " + str(SUPPORTED_THEORIES))
        exit(1)

    endpoint_runtime      = config.get('REQUIRED', 'EndpointRuntime', fallback=None)
    endpoint_fmf          = config.get('REQUIRED', 'EndpointFmf', fallback=None)
    endpoint_eager_v_lazy = config.get('REQUIRED', 'EndpointEagerVLazy', fallback=None)

    if endpoint_runtime == None and endpoint_fmf == None and endpoint_eager_v_lazy == None:
        print("You must pass an endpoint for at least one of the models.")
        exit(1)


    # Get optional options

    # If not defined, sets the fallback value to None
    # That is, we MUST check that these values are not None
    # before using them
    solver         = config.get('OPTIONAL', 'Solver',         fallback=None)
    fmf            = config.get('OPTIONAL', 'FMF',            fallback=None)
    feature_means1 = config.get('OPTIONAL', 'M1FeatureMeans', fallback=None)
    feature_stds1  = config.get('OPTIONAL', 'M1FeatureStds',  fallback=None)
    buckets        = config.get('OPTIONAL', 'Buckets',        fallback=None)
    v              = config.get('OPTIONAL', 'Verbosity',      fallback='Full')

    # Load in the fmf option, if provided
    if fmf == 'True': fmf = True
    else:             fmf = False


    # Alerts the user to a potential mistake, but does not exit as the Runtime Prediction Model can still be evaluated.
    if fmf and endpoint_fmf == None:
      print("Warning: The FMF option was set to True in the config file, but an endpoint name was not passed for the Solver Configuration Model.")


    # json.loads() casts the String inputs to a Python list

    if not feature_means1 == None:
        feature_means1 = json.loads(feature_means1)

    if not feature_stds1 == None:
        feature_stds1 = json.loads(feature_stds1)
  
    if not buckets == None:
        buckets = json.loads(buckets)


    if theory == "QF_SLIA":
        on_features = do_runtime_prediction(problem_file, endpoint_runtime)
        if fmf:       do_solver_configuration(theory, endpoint_fmf, on_features)

    elif theory == "QF_IDL" or theory == "QF_LIA":
        do_eager_lazy(problem_file, endpoint_eager_v_lazy)

