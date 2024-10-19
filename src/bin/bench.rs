use std::fs;
use std::fs::File;
use std::iter;
use std::path::Path;
use std::time::Duration;

use anyhow::{Result, anyhow};
use clap::Parser as _;
use flexi_logger::Logger;
use rand::prelude::*;
use smt_str_solver::*;

#[derive(clap::Parser)]
#[command(version, about, author)]
struct Cli {
  #[command(subcommand)]
  subcmd: Subcmd,
  /// Timeout for each formula in seconds.
  #[arg(short, long, default_value_t = 16.0)]
  timeout: f64,
  /// Be verbose and print out every formula we solve.
  #[arg(short, long)]
  verbose: bool,
  /// Be super verbose and print lots of trace debug info.
  #[arg(short, long)]
  debug: bool,
}

#[derive(clap::Subcommand)]
enum Subcmd {
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
  let log_level = if cli.debug {
    "trace"
  } else if cli.verbose {
    "info"
  } else {
    "warn"
  };
  Logger::try_with_env_or_str(log_level)
    .unwrap()
    .format(|f, _, r| write!(f, "{}", r.args()))
    .log_to_stdout()
    .start()
    .unwrap();
  let timeout = Some(Duration::from_secs_f64(cli.timeout));
  match cli.subcmd {
    Subcmd::Random1 { n, only } => {
      if let Some(only) = only {
        run_benchmark(
          iter::once(
            random_formulae(n)
              .nth(only - 1)
              .ok_or_else(|| anyhow!("{only} out of range"))?,
          ),
          timeout,
          None,
        )
      } else {
        run_benchmark(random_formulae(n), timeout, None)
      }
    }
    Subcmd::Benchmark1 { n } => {
      if let Some(n) = n {
        run_benchmark(benchmark_n("benchmark_1")?.take(n), timeout, None)
      } else {
        run_benchmark(benchmark_n("benchmark_1")?, timeout, None)
      }
    }
    Subcmd::Benchmark2 { n } => {
      if let Some(n) = n {
        run_benchmark(benchmark_n("benchmark_2")?.take(n), timeout, None)
      } else {
        run_benchmark(benchmark_n("benchmark_2")?, timeout, None)
      }
    }
  }
}

type SolverResult = (Formula, Solution, NodeStats);

fn run_benchmark(
  formulae: impl ExactSizeIterator<Item = Formula>,
  timeout: Option<Duration>,
  results_file: Option<&Path>,
) -> Result<()> {
  let mut results: Vec<SolverResult> = Vec::new();
  for (i, formula) in formulae.enumerate() {
    log::info!("Formula {}: {formula}", i + 1);
    let (mut solution, stats) = solve(formula.clone(), CollectNodeStats::from_now(timeout));
    let stats = stats.finished();
    log::info!("  {solution}; {stats}");
    if let Sat(x) = &mut solution {
      x.assert_correct();
    }
    results.push((formula, solution, stats));
  }
  if let Some(path) = results_file {
    bincode::serialize_into(File::create(path)?, &results)?;
  }
  summerize_results(&results);
  Ok(())
}

fn summerize_results(results: &[SolverResult]) {
  // All results which are not cancelled, that is SAT or UNSAT.
  let mut n_sat = 0;
  let mut completed_results = results
    .iter()
    .filter_map(|x| match x.1 {
      Sat(_) => {
        n_sat += 1;
        Some(x)
      }
      Unsat => Some(x),
      Cancelled => None,
    })
    .collect::<Vec<&SolverResult>>();
  println!(
    "{}/{} ({:.1} %) formulae was solved without a timeout.",
    completed_results.len(),
    results.len(),
    100.0 * completed_results.len() as f64 / results.len() as f64
  );
  println!(
    "{n_sat} satisfiable and {} unsatisfiable formulae.",
    completed_results.len() - n_sat
  );
  if completed_results.len() > 0 {
    let mut table = comfy_table::Table::new();
    let percentiles = [0.0, 2.5, 50.0, 97.5, 100.0];
    table
      .load_preset(comfy_table::presets::ASCII_FULL_CONDENSED)
      .set_header([
        "",
        "Average",
        "Min",
        "2.5 percentile",
        "Median",
        "97.5 percentile",
        "Max",
      ])
      .add_row(
        [
          "Search time".to_string(),
          format_duration(
            completed_results
              .iter()
              .map(|x| x.2.search_time)
              .sum::<Duration>()
              / completed_results.len() as u32,
          )
          .to_string(),
        ]
        .into_iter()
        .chain(
          get_percentiles(percentiles, &mut completed_results, |(_, _, stats)| {
            stats.search_time.as_secs_f64()
          })
          .map(|x| format_duration(Duration::from_secs_f64(x)).to_string()),
        ),
      )
      .add_row(
        [
          "Nodes".to_string(),
          format!(
            "{:.3}",
            (completed_results
              .iter()
              .map(|x| x.2.node_count as f64)
              .sum::<f64>()
              / completed_results.len() as f64)
          ),
        ]
        .into_iter()
        .chain(
          get_percentiles(percentiles, &mut completed_results, |(_, _, stats)| {
            stats.node_count as f64
          })
          .map(|x| (x as usize).to_string()),
        ),
      )
      .add_row(
        [
          "Mean node time".to_string(),
          format_duration(Duration::from_secs_f64(
            completed_results
              .iter()
              .map(|x| x.2.search_time.as_secs_f64())
              .sum::<f64>()
              / completed_results
                .iter()
                .map(|x| x.2.node_count)
                .sum::<usize>() as f64,
          ))
          .to_string(),
        ]
        .into_iter()
        .chain(
          get_percentiles(percentiles, &mut completed_results, |(_, _, stats)| {
            stats.search_time.as_secs_f64() / stats.node_count as f64
          })
          .map(|x| format_duration(Duration::from_secs_f64(x)).to_string()),
        ),
      )
      .add_row(
        [
          "Max physical mem".to_string(),
          format!(
            "{:.3}",
            (completed_results
              .iter()
              .map(|x| x.2.max_physical_mem)
              .sum::<f64>()
              / completed_results.len() as f64)
          ),
        ]
        .into_iter()
        .chain(
          get_percentiles(percentiles, &mut completed_results, |(_, _, stats)| {
            stats.max_physical_mem
          })
          .map(|x| (x as usize).to_string()),
        ),
      )
      .add_row(
        [
          "Max virtual mem".to_string(),
          format!(
            "{:.3}",
            (completed_results
              .iter()
              .map(|x| x.2.max_virtual_mem)
              .sum::<f64>()
              / completed_results.len() as f64)
          ),
        ]
        .into_iter()
        .chain(
          get_percentiles(percentiles, &mut completed_results, |(_, _, stats)| {
            stats.max_virtual_mem
          })
          .map(|x| (x as usize).to_string()),
        ),
      );
    println!("{table}");
  }
}

/// Given a list of items, sort those items and  compute a number of percentiles.
///
/// # Arguments
///
/// `percentiles` An iterator of the percentiles we want. In the range `0.0..=100.0`.
/// `items` A mutible non-empty slice of items. It will be sorted but no item will be changed.
/// `key` A key function which takes an item and returns a `f64`.
///
/// # Returns
///
/// Returns an iterator of the percentiles.
fn get_percentiles<'a, T>(
  percentiles: impl IntoIterator<Item = f64> + 'a,
  items: &'a mut [T],
  key: impl Fn(&T) -> f64 + 'a,
) -> impl Iterator<Item = f64> + 'a {
  assert!(!items.is_empty());
  items.sort_unstable_by(|x, y| f64::total_cmp(&key(x), &key(y)));
  percentiles.into_iter().map(move |percentile| {
    let index = percentile / 100.0 * items.len() as f64;
    let int_index: usize = index.ceil() as usize;
    if int_index == 0 {
      key(&items[0])
    } else if index.fract() == 0.0 && int_index < items.len() {
      (key(&items[int_index - 1]) + key(&items[int_index])) / 2.0
    } else {
      key(&items[int_index - 1])
    }
  })
}

fn random_formulae(n: usize) -> impl ExactSizeIterator<Item = Formula> {
  let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(42);
  let var_names: [&str; 8] = ["X", "Y", "Z", "U", "V", "W", "P", "Q"];
  // The 286th iteration takes a lot of time.
  (0..n).map(move |_| {
    let n_clauses = rng.gen_range(0..=3);
    let mut lhss = Vec::<String>::with_capacity(n_clauses);
    let mut rhss = Vec::<String>::with_capacity(n_clauses);
    for _ in 0..n_clauses {
      let str_len = rng.gen_range(0..=8);
      let string = (0..str_len)
        .map(|_| if rng.gen() { 'a' } else { 'b' })
        .collect::<String>();
      lhss.push(string.clone());
      rhss.push(string);
    }
    let n_variables = rng.gen_range(0..8);
    let mut vars = Vec::with_capacity(n_variables);
    for i in 0..n_variables {
      let len = rng.gen_range(0..4);
      let val = (0..len)
        .map(|_| if rng.gen() { 'a' } else { 'b' })
        .collect::<String>();
      vars.push((var_names[i], val));
    }
    // Replace substrings equal to any variable with a probability of 3/4.
    for (var_name, val) in vars {
      for xhs in lhss.iter_mut().chain(rhss.iter_mut()) {
        while rng.gen_bool(0.75) {
          let Some(i) = xhs.find(&val) else {
            break;
          };
          xhs.replace_range(i..(i + val.len()), var_name);
        }
      }
    }
    Formula::from_strs(
      &lhss
        .iter()
        .zip(rhss.iter())
        .map(|(lhs, rhs)| (lhs.as_str(), rhs.as_str()))
        .collect::<Vec<_>>(),
      |x| char::is_ascii_uppercase(&x),
    )
  })
}

/// A sorted iterator of all formulae in benchmark_1.
fn benchmark_n(dir: &str) -> Result<impl ExactSizeIterator<Item = Formula>> {
  let mut files = fs::read_dir(dir)?
    .map(|entry| Ok(entry?.path()))
    .collect::<Result<Vec<_>>>()?;
  files.sort();
  files
    .into_iter()
    .map(|f| Formula::from_eq_file(&fs::read_to_string(f)?))
    .collect::<Result<Vec<_>>>()
    .map(|x| x.into_iter())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_percentile() {
    let mut nums = [4.0, 1.5, 2.0, 1.0];
    assert_eq!(
      get_percentiles(
        [0.0, 20.0, 25.0, 30.0, 50.0, 60.0, 75.0, 80.0, 100.0],
        &mut nums,
        |x| *x
      )
      .collect::<Vec<_>>(),
      [1.0, 1.0, 1.25, 1.5, 1.75, 2.0, 3.0, 4.0, 4.0]
    );
  }
}
