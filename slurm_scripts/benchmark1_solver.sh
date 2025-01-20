#!/bin/bash -l
#SBATCH -A uppmax2024-2-18
#SBATCH -M snowy
#SBATCH -p core
#SBATCH -n 1
#SBATCH -t 0:5:00
#SBATCH -J wordeq_benchmark_1

cargo r -r -- \
  -p1 -vt300 \
  --bincode "res_b1.bincode" \
  benchmark b1
