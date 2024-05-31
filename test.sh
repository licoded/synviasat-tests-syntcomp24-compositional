#!/bin/bash
# 366 459 464

touch os_log

for i in {1..500}
do
    echo ${i}
    (export SAT_TRACE=1 ; ./ltlfsyn ~/correct_bench/f${i}.ltlf ~/correct_bench/f${i}.var ) >> os_log
done