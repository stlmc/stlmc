#!/bin/bash
# bash specific script!!
for (( c=$1; c<=$2; c=c+$3 ))
do
        echo "Welcome $c times"
        for (( d=1; d<=10; d=d+1 ))
        do
                echo "Run formula $d normal"
                sbatch ./stlmc-test ./experiment/stl/onlySTL.model -l $c -u $c -formula_num $d -formula_encoding only-goal-stl -solver yices
                echo "Run formula $d enhanced"
		ff="$((8 * $c))"
                sbatch ./stlmc-test ./experiment/stl/onlySTL.model -l $ff -u $ff -formula_num $d -formula_encoding only-goal-stl-enhanced -solver yices
        done
done
