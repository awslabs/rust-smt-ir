#!/bin/bash
# Runs the `get_solver_output.py` script
# - In the background (nohup + &)
# - With unbuffered output (-u) so that nohup can send output to nohup.out
# - On the set of benchmarks which were slower with --strings-fmf
nohup python3 -u get_solver_output.py cvc4 ../SMT_Comp_2020/experiments_CVC4_FMF/slower_fmf.csv ../SMT_Comp_2020 &
