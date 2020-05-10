#!/bin/sh
#SBATCH -J stlz3Run
#SBATCH -p cpu
#SBATCH -N 1
#SBATCH -n 1
#SBATCH -o runz3STL
#SBATCH -e errorz3STL
#SBATCH --comment
#SBATCH --time 24:00:00
#SBATCH --gres=gpu:2

srun stlmc twoCarLinear.model -solver yices -l 10 -u 50 -s 10 -logic qf_lra -visualize true -log true 


