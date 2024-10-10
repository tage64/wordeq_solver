use smt_str_solver::vec_list::VecList;
use smt_str_solver::*;

#[test]
fn test_simple_equations() {
  let formula_1 = Formula::new(Cnf(VecList::new()), Vec::new());
  solve_no_timeout(formula_1).assert_sat();
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
  solve_no_timeout(formula_2).assert_sat();
  let formula_3 = Formula::new(
    Cnf(
      [Clause {
        equation: Equation {
          lhs: Word([Term::Terminal(Terminal('a'))].into_iter().collect()),
          rhs: Word(VecList::new()),
        },
      }]
      .into_iter()
      .collect(),
    ),
    Vec::new(),
  );
  solve_no_timeout(formula_3).assert_unsat();
}
