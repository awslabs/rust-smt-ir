#!/bin/bash

list_file=$1
solver=$2
test_path=$3
use_global_map=$4
shift; shift; shift; shift;

setsid nohup parallel -j 20 -a $list_file --timeout 3600 --joblog job.log ./test_and_transform.sh $solver ${test_path}/{} $use_global_map $@

