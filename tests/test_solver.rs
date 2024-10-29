use std::time::Duration;

use smt_str_solver::benchmarks::*;
use smt_str_solver::vec_list::VecList;
use smt_str_solver::*;

#[test]
fn test_simple_equations() {
  let formula_1 = Formula::new(Cnf(VecList::new()), Vec::new());
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
  );
  solve_simple(formula_2).assert_sat();
  let formula_3 = Formula::new(
    Cnf(
      [Clause {
        equation: Equation {
          lhs: Word([Term::Terminal(Terminal("a".into()))].into_iter().collect()),
          rhs: Word(VecList::new()),
        },
      }]
      .into_iter()
      .collect(),
    ),
    Vec::new(),
  );
  solve_simple(formula_3).assert_unsat();
}

#[test]
fn random1_single_threaded() {
  let results = run_benchmark(
    random_formulae(1000),
    Duration::from_secs(8),
    1.try_into().unwrap(),
  )
  .unwrap();
  for (_, result, _) in results.into_iter() {
    result.assert_sat();
  }
}

#[test]
fn random1_multi_threaded() {
  let results = run_benchmark(
    random_formulae(1000),
    Duration::from_secs(8),
    4.try_into().unwrap(),
  )
  .unwrap();
  for (_, result, _) in results.into_iter() {
    result.assert_sat();
  }
}
