#!/bin/bash -l
#SBATCH -A uppmax2024-2-18
#SBATCH -M snowy
#SBATCH -p core
#SBATCH -n 16
#SBATCH -t 7:00:00
#SBATCH -a 0-950:50
#SBATCH -J str_solver_benchmark_parallelism

SKIP=$SLURM_ARRAY_TASK_ID
TAKE=$(($SLURM_ARRAY_TASK_ID + 50))
cargo r -r -- \
  -p16 -vt300 \
  --skip $SKIP \
  --take $TAKE \
  --bincode "res_${SKIP}_${TAKE}.bincode" \
  benchmark b2
