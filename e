#!/bin/bash
# bash specific script!!
model=$1
for (( c=$2; c<=$3; c=c+$4 ))
do
        echo "Welcome $c times"
        for (( d=$5; d<=$6; d=d+$7 ))
        do
                echo "Run formula $d at $1 with bound $c"
                sbatch ./stlmc-test $model -l $c -u $c -formula_num $d -formula_encoding model-with-goal -solver yices -verbose true
                #echo "Run formula $d enhanced"
		#ff="$((8 * $c))"
                #sbatch ./stlmc-test ./experiment/stl/onlySTL.model -l $ff -u $ff -formula_num $d -formula_encoding only-goal-stl-enhanced -solver yices
        done
done
