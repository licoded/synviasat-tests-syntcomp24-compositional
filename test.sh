#!/bin/bash
# 366 459 464

touch os_log

for i in {1..500}
do
    echo ${i}
    ./ltlfsyn ~/correct_bench1/f${i}.ltlf ~/correct_bench1/f${i}.var 1 >> os_log
done