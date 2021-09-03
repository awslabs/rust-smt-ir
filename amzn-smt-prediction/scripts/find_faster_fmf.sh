#!/bin/bash
# Runs the `find_faster.py` script
# - In the background (nohup + &)
# - With unbuffered output (-u) so that nohup can send output to nohup.out
nohup python3 -u find_faster_fmf.py ../SMT_Comp_2020/experiments_QF_SLIA/benchmarks_QF_SLIA_30-to-300.csv ../SMT_Comp_2020/ &
