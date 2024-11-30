#!/bin/bash -l
#SBATCH -A uppmax2024-2-18
#SBATCH -M snowy
#SBATCH -p core
#SBATCH -n 16
#SBATCH -t 7:00:00
#SBATCH -a 1-951:50
#SBATCH -J str_solver_benchmark_parallelism

cargo r -r -- \
  -p16 -vt300 \
  --skip $SLURM_ARRAY_TASK_ID \
  --take $(($SLURM_ARRAY_TASK_ID + 49)) \
  --bincode "res_${SLURM_ARRAY_TASK_ID}_$(($SLURM_ARRAY_TASK_ID + 49)).bincode" \
  benchmark b2
