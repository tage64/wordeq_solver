use std::fs;
use std::io::{self, Read};
use std::iter;
use std::num::NonZero;
use std::path::PathBuf;
use std::thread::available_parallelism;
use std::time::Duration;

use anyhow::{Result, anyhow};
use clap::Parser as _;
use flexi_logger::{LogSpecification, Logger};
use log::LevelFilter::*;
use smt_str_solver::benchmarks::*;
use smt_str_solver::*;

const PRINT_STATS_INTERVAL: Duration = Duration::from_millis(1000);

#[derive(clap::Parser)]
#[command(version, about, author)]
struct Cli {
  #[command(subcommand)]
  subcmd: Subcmd,
  /// Timeout for each formula in seconds.
  #[arg(short, long, default_value_t = 16.0)]
  timeout: f64,
  /// The number of threads, defaults to to the available number of threads on the system.
  #[arg(short = 'p', long)]
  threads: Option<NonZero<u32>>,
  /// Print out the running time and the solution.
  #[arg(short, long)]
  verbose: bool,
  /// Be super verbose and print lots of trace debug info. (Requires the trace_logging feature.)
  #[arg(short, long)]
  debug: bool,
  /// Print memory statistics with regular intervals. (Requires the trace_logging feature.)
  #[arg(short, long)]
  mem_info: bool,
}

#[derive(clap::Subcommand)]
enum Subcmd {
  /// Solve a single formula.
  Solve {
    /// Read a .eq file, otherwise read equations line by line from STDIN where uppercase letters are
    /// variables.
    eq_file: Option<PathBuf>,
  },
  /// Benchmark small randomly but deterministically generated formulae.
  Random1 {
    /// The number of formulae.
    #[arg(default_value_t = 1000)]
    n: usize,
    /// Solve only the nth formula
    #[arg(short, long)]
    only: Option<usize>,
  },
  /// Run benchmark 1.
  Benchmark1 {
    /// Run only the n first formulae.
    n: Option<usize>,
  },
  /// Run benchmark 2.
  Benchmark2 {
    /// Run only the n first formulae.
    n: Option<usize>,
  },
}

fn main() -> Result<()> {
  let cli = Cli::parse();
  let mut log_spec_builder = LogSpecification::builder();
  log_spec_builder.default(if cli.verbose { Info } else { Warn });
  if cli.debug {
    log_spec_builder.module("smt_str_solver", Trace);
  }
  if cli.mem_info {
    log_spec_builder.module("smt_str_solver::node_watcher", Trace);
  }
  Logger::with(log_spec_builder.build())
    .format(|f, _, r| write!(f, "{}", r.args()))
    .log_to_stdout()
    .start()
    .unwrap();
  let timeout = Duration::from_secs_f64(cli.timeout);
  let n_threads = if let Some(x) = cli.threads {
    x
  } else {
    let threads = available_parallelism()?;
    log::info!("Using {} threads.", threads.get());
    threads.try_into().unwrap()
  };
  match cli.subcmd {
    Subcmd::Solve { eq_file } => {
      let formula = if let Some(eq_file) = eq_file {
        Formula::from_eq_file(&fs::read_to_string(eq_file)?)?
      } else {
        let mut stdin = String::new();
        io::stdin().lock().read_to_string(&mut stdin)?;
        Formula::from_strs(
          &stdin
            .lines()
            .map(|line| {
              line
                .split_once(" = ")
                .ok_or_else(|| anyhow!("The LHS and RHS should be separated by \" = \""))
            })
            .collect::<Result<Vec<_>>>()?,
          char::is_uppercase,
        )
      };
      let (mut solution, stats) = solve(
        formula.clone(),
        CollectNodeStats::from_now(
          timeout,
          if cli.mem_info {
            Some(PRINT_STATS_INTERVAL)
          } else {
            None
          },
        ),
        n_threads,
      );
      println!("{solution}; {stats}");
      if let Sat(x) = &mut solution {
        x.assert_correct();
        log::info!("{}", x.display());
      }
    }
    Subcmd::Random1 { n, only } => {
      if let Some(only) = only {
        run_benchmark(
          iter::once(
            random_formulae(n)
              .nth(only - 1)
              .ok_or_else(|| anyhow!("{only} out of range"))?,
          ),
          timeout,
          n_threads,
        )?;
      } else {
        run_benchmark(random_formulae(n), timeout, n_threads)?;
      }
    }
    Subcmd::Benchmark1 { n } => {
      if let Some(n) = n {
        run_benchmark(benchmark_n("benchmark_1")?.take(n), timeout, n_threads)?;
      } else {
        run_benchmark(benchmark_n("benchmark_1")?, timeout, n_threads)?;
      }
    }
    Subcmd::Benchmark2 { n } => {
      if let Some(n) = n {
        run_benchmark(benchmark_n("benchmark_2")?.take(n), timeout, n_threads)?;
      } else {
        run_benchmark(benchmark_n("benchmark_2")?, timeout, n_threads)?;
      }
    }
  }
  Ok(())
}
