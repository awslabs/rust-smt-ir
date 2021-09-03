# Eager v. Lazy Experiment Data Collection

## Data

``{idl,lia}_results.csv``: Contains the runtime of CVC4, Z3, and the Eager Approach via SAT on a set of benchmarks from SMT Comp 2020.

``{idl,lia}_params.out``: Contains the statistics generated while encoding each benchmark for the Eager Approach.

The script ``clean_eager_lazy_data.py`` is ran on the above files to transform them into ``benchmarks_{idl,lia}.csv``, ``features_{idl,lia}.csv``, and ``best_solver_{idl,lia}.csv``, which contain the set of benchmarks, the corresponding features to the model (computed from the Eager Approach encoding statistics), and the corresponding fastest solver.

