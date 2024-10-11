use std::fs::File;
use std::path::Path;
use std::time::Duration;

use flexi_logger::Logger;
use rand::prelude::*;
use smt_str_solver::*;

type Results = Vec<(Formula, Solution, NodeStats)>;

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
  let mut results: Results = Vec::new();
  for (i, formula) in formulae.enumerate() {
    log::info!("Formula {}: {formula}", i + 1);
    let (mut solution, stats) = solve(
      formula.clone(),
      CollectNodeStats::from_now(Duration::from_secs(32)),
    );
    let stats = stats.finished();
    log::info!("  {stats}");
    if let Sat(x) = &mut solution {
      x.assert_correct();
    }
    results.push((formula, solution, stats));
  }
  if let Some(path) = results_file {
    bincode::serialize_into(File::create(path)?, &results)?;
  }
  Ok(())
}

fn summerize_results(mut results: Results) {
  todo!()
}

fn random_formulae() -> impl ExactSizeIterator<Item = Formula> {
  let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(42);
  let var_names: [&str; 8] = ["X", "Y", "Z", "U", "V", "W", "P", "Q"];
  // The 286th iteration takes a lot of time.
  (0..285).map(move |_| {
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
