#!/bin/bash

for file1 in $1/*_transformed.smtlib; do
        same_count=0
        for file2 in $1/*_transformed.smtlib; do
                diff $file1 $file2 > /dev/null 2>&1
                if [ $? -eq 0 ]; then
                        (( same_count = $same_count + 1 ))
                        echo " --- " $file2
                fi
        done
        echo $file1 " : " $same_count
done
