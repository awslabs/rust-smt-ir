#!/bin/bash
# Runs the `get_solver_output.py` script
# - In the background (nohup + &)
# - With unbuffered output (-u) so that nohup can send output to nohup.out
# - On the set of benchmarks which use --strings-fmf
nohup python3 -u get_solver_output.py cvc4 ../SMT_Comp_2020/experiments_QF_SLIA/benchmarks_QF_SLIA_30-to-300.csv ../SMT_Comp_2020 &
