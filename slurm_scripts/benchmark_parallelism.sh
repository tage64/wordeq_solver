#!/bin/bash -l
#SBATCH -A uppmax2024-2-18
#SBATCH -p node
#SBATCH -t 00:04:00
#SBATCH -J str_solver_benchmark_parallelism

cargo r -r -- -p8 -vt10 --only 3 benchmark b2
cargo r -r -- -p9 -vt10 --only 3 benchmark b2
cargo r -r -- -p10 -vt10 --only 3 benchmark b2
cargo r -r -- -p11 -vt10 --only 3 benchmark b2
cargo r -r -- -p12 -vt10 --only 3 benchmark b2
cargo r -r -- -p13 -vt10 --only 3 benchmark b2
cargo r -r -- -p14 -vt10 --only 3 benchmark b2
cargo r -r -- -p15 -vt10 --only 3 benchmark b2
cargo r -r -- -p16 -vt10 --only 3 benchmark b2
