# Eager v. Lazy Experiment (Full) Data Collection

## Data

This is an extension of the original Eager v. Lazy Experiment in which I ran CVC4, Z3, and the Eager Approach on all problems in the QF_IDL benchmark set from SMT Comp 2020 (834 problems). The script ``run_eager_v_lazy.py`` does this.

Due to limited time, I only ran each on a timeout of 5 minutes. In the future, this experiment should be repeated with a longer timeout (1 hour) to ensure that all instances where the Eager Approach is faster are captured. It should
also be ran on the QF_LIA benchmarks. This set is larger (~2000 problems) and there wasn't enough time left in my internship for my script to run on all of these.

## Known Issues

Z3 can't solve problems whose filenames contain an equals symbol, as it interprets it as a solver option. Therefore I used the following command to replace all equals signs in filenames with underscores. (Note that this uses the command ``replace``, available on Mac via Homebrew.). From the directory ``SMT_Comp_2020/non-incremental/QF_IDL/asp`` (there were no filenames with equals signs in any other subfolder):

``find -d ./ -type f -execdir rename 's/=/_/g' '{}' \;``

