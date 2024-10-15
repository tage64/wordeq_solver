use std::fs::File;
use std::iter;
use std::path::Path;
use std::time::Duration;

use flexi_logger::Logger;
use humantime::format_duration;
use rand::prelude::*;
use smt_str_solver::*;

type SolverResult = (Formula, Solution, NodeStats);

fn main() -> anyhow::Result<()> {
  run_benchmark(random_formulae(), None)
}

fn run_benchmark(
  formulae: impl ExactSizeIterator<Item = Formula>,
  results_file: Option<&Path>,
) -> anyhow::Result<()> {
  #[allow(unused_variables, unused_mut)]
  let mut logger = Logger::try_with_env_or_str("info")
    .unwrap()
    .format(|f, _, r| write!(f, "{}", r.args()))
    .log_to_stdout()
    .start()
    .unwrap();
  let mut results: Vec<SolverResult> = Vec::new();
  for (i, formula) in formulae.enumerate() {
    log::info!("Formula {}: {formula}", i + 1);
    let (mut solution, stats) = solve(
      formula.clone(),
      CollectNodeStats::from_now(Duration::from_secs(16)),
    );
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
  let mut completed_results = results
    .iter()
    .filter_map(|x| match x.1 {
      Sat(_) | Unsat => Some(x),
      Cancelled => None,
      Unknown => unreachable!(),
    })
    .collect::<Vec<&SolverResult>>();
  println!(
    "{}/{} ({:.1} %) formulae was solved without a timeout.",
    completed_results.len(),
    results.len(),
    100.0 * completed_results.len() as f64 / results.len() as f64
  );
  let mut table = comfy_table::Table::new();
  table
    .load_preset(comfy_table::presets::ASCII_FULL_CONDENSED)
    .set_header(["", "Q1", "Median", "Q3"])
    .add_row(
      iter::once("Search time".to_string()).chain(
        get_percentiles(
          [25.0, 50.0, 75.0],
          &mut completed_results,
          |(_, _, stats)| stats.search_time.as_secs_f64(),
        )
        .map(|x| format_duration(Duration::from_secs_f64(x)).to_string()),
      ),
    )
    .add_row(
      iter::once("Nodes".to_string()).chain(
        get_percentiles(
          [25.0, 50.0, 75.0],
          &mut completed_results,
          |(_, _, stats)| stats.node_count as f64,
        )
        .map(|x| (x as usize).to_string()),
      ),
    )
    .add_row(
      iter::once("Mean node time".to_string()).chain(
        get_percentiles(
          [25.0, 50.0, 75.0],
          &mut completed_results,
          |(_, _, stats)| stats.search_time.as_secs_f64() / stats.node_count as f64,
        )
        .map(|x| format_duration(Duration::from_secs_f64(x)).to_string()),
      ),
    );
  println!("{table}");
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

fn random_formulae() -> impl ExactSizeIterator<Item = Formula> {
  let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(42);
  let var_names: [&str; 8] = ["X", "Y", "Z", "U", "V", "W", "P", "Q"];
  // The 286th iteration takes a lot of time.
  (0..8).map(move |_| {
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
