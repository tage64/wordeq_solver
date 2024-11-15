use std::time::Duration;

use smt_str_solver::benchmarks::*;
use smt_str_solver::vec_list::VecList;
use smt_str_solver::*;

#[test]
fn test_simple_equations() {
  let formula_1 = Formula::new(Cnf(VecList::new()), Vec::new(), Vec::new());
  solve_simple(formula_1).assert_sat();
  let formula_2 = Formula::new(
    Cnf(
      [Clause {
        equation: Equation {
          lhs: Word(VecList::new()),
          rhs: Word(VecList::new()),
        },
      }]
      .into_iter()
      .collect(),
    ),
    vec!["X".into(), "Y".into()],
    Vec::new(),
  );
  solve_simple(formula_2).assert_sat();
  let formula_3 = Formula::new(
    Cnf(
      [Clause {
        equation: Equation {
          lhs: Word(
            [Term::Terminal(Terminal(Box::new([0])))]
              .into_iter()
              .collect(),
          ),
          rhs: Word(VecList::new()),
        },
      }]
      .into_iter()
      .collect(),
    ),
    Vec::new(),
    vec!['a'],
  );
  solve_simple(formula_3).assert_unsat();
}

#[test]
fn random1() {
  let single_thread = run_benchmark(
    random_formulae(200),
    Duration::from_secs(8),
    1.try_into().unwrap(),
  )
  .unwrap();
  let multi_thread = run_benchmark(
    random_formulae(200),
    Duration::from_secs(8),
    4.try_into().unwrap(),
  )
  .unwrap();
  for (i, (single_thread, multi_thread)) in single_thread
    .into_iter()
    .zip(multi_thread.into_iter())
    .enumerate()
  {
    single_thread.1.assert_sat();
    multi_thread.1.assert_sat();
    assert_eq!(
      single_thread.2.max_depth,
      multi_thread.2.max_depth,
      "Max depth of single and multi threaded searches differ at formula {}",
      i + 1
    );
  }
}
