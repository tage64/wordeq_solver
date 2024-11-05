use std::cell::{OnceCell, RefCell};
use std::fmt;

use compact_str::CompactString;
use derive_more::Display;
use serde::{Deserialize, Serialize};
use vec_map::VecMap;

use super::SearchNode;
use crate::*;

#[derive(Debug, Display, Serialize, Deserialize)]
pub enum Solution {
  #[display("SAT")]
  Sat(SatResult),
  #[display("UNSAT")]
  Unsat,
  Cancelled,
}
pub use Solution::*;

/// A struct returned for a satisfying solution from which it is possible to get the values for all
/// variables.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SatResult {
  formula: Formula,
  assignments: VecMap<Word>,
  /// Cached string values for variables.
  #[serde(skip)]
  cached_assignments: RefCell<VecMap<CompactString>>,
  /// The formula where all variables have been substituted to a satisfying solution.
  #[serde(skip)]
  substituted_formula: OnceCell<Vec<(CompactString, CompactString)>>,
}

impl Solution {
  /// Get a `SatResult` if it is SAT else `None`.
  pub fn get_sat(self) -> Option<SatResult> {
    if let Sat(x) = self { Some(x) } else { None }
  }

  /// Convenience function to check that this is a correct satisfying solution.
  pub fn assert_sat(self) -> SatResult {
    let Sat(mut sat_res) = self else {
      panic!("Expected a satisfying solution, but it is {self}")
    };
    sat_res.assert_correct();
    sat_res
  }

  /// Convenience function to assert that the solution is UNSAT.
  pub fn assert_unsat(&self) {
    let Unsat = self else {
      panic!("Expected solution to be UNSAT but it is {self}");
    };
  }
}

impl SatResult {
  pub(super) fn new<W>(node: SearchNode<W>) -> Self {
    Self {
      formula: node.shared_info.original_formula.clone(),
      assignments: node.assignments,
      cached_assignments: RefCell::new(VecMap::new()),
      substituted_formula: OnceCell::new(),
    }
  }

  /// Get all clauses ((LHS, RHS) pairs) where all variables have been replaced by terminals
  /// to form a satisfying solution.
  pub fn substituted_formula(&self) -> &Vec<(CompactString, CompactString)> {
    self.substituted_formula.get_or_init(|| {
      let mut substituted_formula = Vec::new();
      for (_, clause) in self.formula.cnf.0.iter() {
        let mut substituted_lhs = CompactString::default();
        for (_, term) in clause.equation.lhs.0.iter() {
          match term {
            Term::Terminal(Terminal(s)) => substituted_lhs += s,
            Term::Variable(var) => substituted_lhs += &self.get_var(*var),
          }
        }
        let mut substituted_rhs = CompactString::default();
        for (_, term) in clause.equation.rhs.0.iter() {
          match term {
            Term::Terminal(Terminal(s)) => substituted_rhs += s,
            Term::Variable(var) => substituted_rhs += &self.get_var(*var),
          }
        }
        substituted_formula.push((substituted_lhs, substituted_rhs));
      }
      substituted_formula
    })
  }

  /// Get a value for a variable which contribute to a satisfying solution.
  pub fn get_var(&self, var: Variable) -> CompactString {
    if let Some(x) = self.cached_assignments.borrow().get(var.id) {
      return x.clone();
    }
    let val = if let Some(assignment) = self.assignments.get(var.id) {
      assignment
        .0
        .iter()
        .filter_map(|(_, term)| {
          if let Term::Terminal(Terminal(s)) = term {
            Some(s.as_str())
          } else {
            None
          }
        })
        .collect()
    } else {
      Default::default()
    };
    self.cached_assignments.borrow_mut().insert(var.id, val);
    self.cached_assignments.borrow()[var.id].clone()
  }

  /// Check that the solution is correct.
  pub fn assert_correct(&mut self) {
    for (lhs, rhs) in self.substituted_formula() {
      if lhs != rhs {
        panic!("The solution is not correct: {}.", self.display());
      }
    }
  }

  pub fn display(&mut self) -> impl fmt::Display + '_ {
    struct Displayer<'a>(RefCell<&'a mut SatResult>);

    impl<'a> fmt::Display for Displayer<'a> {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "\nOriginal equations: {}", self.0.borrow().formula)?;
        write!(f, "Substituted equations:")?;
        for (lhs, rhs) in self.0.borrow_mut().substituted_formula() {
          write!(f, " {lhs} = {rhs};")?;
        }
        write!(f, "\nAssignments:")?;
        let var_names = self.0.borrow_mut().formula.var_names.clone();
        for (id, var_name) in var_names.into_iter().enumerate() {
          write!(
            f,
            " {var_name} = {}",
            self.0.borrow_mut().get_var(Variable { id })
          )?;
        }
        writeln!(f)
      }
    }

    Displayer(RefCell::new(self))
  }
}
