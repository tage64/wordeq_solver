#!/bin/bash -l
#SBATCH -A uppmax2024-2-18
#SBATCH -M snowy
#SBATCH -p node
#SBATCH -t 00:04:00
#SBATCH -J str_solver_benchmark_parallelism

cargo r -r -- -p16 -vt10 --only 3 benchmark b2
cargo r -r -- -p17 -vt10 --only 3 benchmark b2
cargo r -r -- -p18 -vt10 --only 3 benchmark b2
cargo r -r -- -p19 -vt10 --only 3 benchmark b2
cargo r -r -- -p20 -vt10 --only 3 benchmark b2
cargo r -r -- -p21 -vt10 --only 3 benchmark b2
