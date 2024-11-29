use std::fs;
use std::io::{self, Read};
use std::iter;
use std::num::NonZero;
use std::path::PathBuf;
use std::thread::available_parallelism;
use std::time::Duration;

use anyhow::{Context, Result, anyhow};
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
  /// Solve at most n formulae.
  n: Option<usize>,
  /// Solve only the nth formula
  #[arg(short, long)]
  only: Option<usize>,
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
    /// Read one or more .eq files, otherwise read equations line by line from STDIN where
    /// uppercase letters are variables.
    eq_files: Vec<PathBuf>,
  },
  /// Run a benchmark.
  Benchmark {
    #[arg(value_enum)]
    benchmark: Benchmark,
  },
}

#[derive(clap::ValueEnum, Clone, Copy)]
enum Benchmark {
  /// Benchmark small randomly but deterministically generated formulae.
  Rand1,
  /// 1000 small formulae which should be solved under a second.
  B1,
  /// 1000 large formulae. 15-20 % can be solved within a few seconds.
  B2,
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
    available_parallelism()?.try_into().unwrap()
  };
  log::info!("Using {} threads.", n_threads.get());

  // We use dynamic dispatch for the iterator here for convenience. It is not performance
  // critical so it should be fine.
  let mut formulae: Box<dyn ExactSizeIterator<Item = Formula>> = match cli.subcmd {
    Subcmd::Solve { eq_files } => {
      if !eq_files.is_empty() {
        Box::new(
          eq_files
            .into_iter()
            .map(|eq_file| -> Result<_> {
              Ok(Formula::from_eq_file(&fs::read_to_string(eq_file)?)?)
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter(),
        )
      } else {
        let mut stdin = String::new();
        io::stdin().lock().read_to_string(&mut stdin)?;
        Box::new(iter::once(Formula::from_strs(
          &stdin
            .lines()
            .map(|line| {
              line
                .split_once(" = ")
                .ok_or_else(|| anyhow!("The LHS and RHS should be separated by \" = \""))
            })
            .collect::<Result<Vec<_>>>()?,
          char::is_uppercase,
        )))
      }
    }
    Subcmd::Benchmark { benchmark } => match benchmark {
      Benchmark::Rand1 => Box::new(random_formulae(cli.n.unwrap_or(1000))),
      Benchmark::B1 => Box::new(benchmark_n(1)?),
      Benchmark::B2 => Box::new(benchmark_n(2)?),
    },
  };
  if let Some(n) = cli.n {
    formulae = Box::new(formulae.take(n));
  }
  if let Some(only) = cli.only {
    formulae = Box::new(iter::once(formulae.nth(only - 1).with_context(|| {
      format!(
        "There are only {} formulae in this benchmark.",
        formulae.len()
      )
    })?));
  }
  if formulae.len() > 1 {
    run_benchmark(formulae, timeout, n_threads)?;
  } else {
    let Some(formula) = formulae.next() else {
      println!("No formulae.");
      return Ok(());
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
  Ok(())
}
