#!/bin/bash -l
#SBATCH -A uppmax2024-2-18
#SBATCH -p node
#SBATCH -t 00:04:00
#SBATCH -J str_solver_benchmark_parallelism

cargo r -r -- -p1 -vt10 --only 3 benchmark b2
cargo r -r -- -p2 -vt10 --only 3 benchmark b2
cargo r -r -- -p4 -vt10 --only 3 benchmark b2
cargo r -r -- -p8 -vt10 --only 3 benchmark b2
cargo r -r -- -p16 -vt10 --only 3 benchmark b2
cargo r -r -- -p20 -vt10 --only 3 benchmark b2
cargo r -r -- -p24 -vt10 --only 3 benchmark b2
cargo r -r -- -p32 -vt10 --only 3 benchmark b2
cargo r -r -- -p40 -vt10 --only 3 benchmark b2
cargo r -r -- -p41 -vt10 --only 3 benchmark b2
