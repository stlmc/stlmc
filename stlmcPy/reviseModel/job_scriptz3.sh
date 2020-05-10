#!/bin/sh
#SBATCH -J stlz3Run
#SBATCH -p cpu
#SBATCH -N 1
#SBATCH -n 1
#SBATCH -o runSTL
#SBATCH -e errorSTL
#SBATCH --comment
#SBATCH --time 24:00:00
#SBATCH --gres=gpu:2

srun stlmc writing.model -l 5 -u 15 -s 5 -timebound 30 -log true -multy true
