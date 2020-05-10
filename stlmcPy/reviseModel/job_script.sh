#!/bin/sh
#SBATCH -J stlYicesRun
#SBATCH -p cpu
#SBATCH -N 1
#SBATCH -n 1
#SBATCH -o runYicesSTL
#SBATCH -e errorYicesSTL
#SBATCH --comment
#SBATCH --time 24:00:00
#SBATCH --gres=gpu:2

srun stlmc twoBatteryLinear.model -l 5



