#!/bin/sh
#SBATCH -J stlYices60Run
#SBATCH -p cpu
#SBATCH -N 1
#SBATCH -n 1
#SBATCH -o runYices60STL
#SBATCH -e errorYicesSTL
#SBATCH --comment
#SBATCH --time 24:00:00
#SBATCH --gres=gpu:2

srun stlmc writing.model -l 5 -u 15 -s 5 -solver yices -timebound 60 -log true -multy true

