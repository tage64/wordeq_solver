use arrayvec::ArrayVec;
use vec_list::ListPtr;

use super::SearchNode;
use crate::*;

/// Splits from a node in the search tree.
///
/// The splits are from one clause involving one or two variables and 0 or one terminals.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Splits {
  /// One variable equal to only the empty string.
  #[expect(dead_code)]
  Empty(Variable),
  /// One variable equal to the empty string or a terminal followed by a fresh variable.
  EmptyOrTerminal(Variable, Terminal),
  /// Two variables, one from LHS and one from RHS.
  ///
  /// First, the first argument should come from LHS and the second from RHS. After calling
  /// `self.decide_order`, the variable to pick first shall come first. `decide_order()` should
  /// only be called once.
  TwoVars(Variable, Variable),
}

impl Splits {
  /// The number of splits (1..=5).
  pub fn len(&self) -> u32 {
    match self {
      Self::Empty(_) => 1,
      Self::EmptyOrTerminal(_, _) => 2,
      Self::TwoVars(_, _) => 4,
    }
  }

  /// Given a branch index, check whether the split will be a reducing split or not.
  pub fn is_reducing(&self, n: u32, solver: &SearchNode) -> bool {
    match (self, n) {
      (Self::Empty(_), 0)
      | (Self::EmptyOrTerminal(_, _), 0)
      | (Self::TwoVars(_, _), 0)
      | (Self::TwoVars(_, _), 1) => true,
      (Self::EmptyOrTerminal(x, _), 1) => {
        solver.var_ptrs[x.id].len() <= 1 && {
          let (lhs, rhs) = solver.var_ptrs[x.id].values().next().unwrap();
          lhs.len() + rhs.len() <= 1
        }
      }
      (Self::TwoVars(_, _), 2) | (Self::TwoVars(_, _), 3) => false,
      _ => unreachable!(),
    }
  }

  /// Check what variable to consider first in the two variable case.
  pub fn decide_order(self, solver: &SearchNode) -> Self {
    match &self {
      Self::Empty(_) | Self::EmptyOrTerminal(_, _) => self,
      Self::TwoVars(x, y) => {
        // Check if x or y is most common.
        let x_diff = solver.var_ptrs[x.id]
          .iter()
          .map(|(clause_id, (x_in_lhs, x_in_rhs))| {
            let Clause {
              equation: Equation { lhs, rhs },
            } = solver.formula.0.get(ListPtr::from_usize(clause_id));
            x_in_lhs.len() as isize - x_in_rhs.len() as isize + rhs.0.len() as isize
              - lhs.0.len() as isize
          })
          .sum::<isize>();
        let y_diff = solver.var_ptrs[y.id]
          .iter()
          .map(|(clause_id, (y_in_lhs, y_in_rhs))| {
            let Clause {
              equation: Equation { lhs, rhs },
            } = solver.formula.0.get(ListPtr::from_usize(clause_id));
            y_in_rhs.len() as isize - y_in_lhs.len() as isize + lhs.0.len() as isize
              - rhs.0.len() as isize
          })
          .sum::<isize>();
        if x_diff < y_diff {
          Self::TwoVars(*y, *x)
        } else {
          Self::TwoVars(*x, *y)
        }
      }
    }
  }

  /// Get the nth split as a tuple (var, replacement).
  ///
  /// `n` the index of the branch.
  ///
  /// Returns a `(variable, assignment)` pair where `variable` is the variable to be
  /// assigned and `assignment` is the terms to assign to the variable.
  pub fn get(&self, n: u32) -> (Variable, ArrayVec<Term, 2>) {
    match (self, n) {
      (Self::Empty(x), 0) | (Self::EmptyOrTerminal(x, _), 0) => (*x, ArrayVec::new()),
      (Self::EmptyOrTerminal(x, a), 1) => (*x, [Term::Terminal(*a), Term::Variable(*x)].into()),
      (Self::TwoVars(x, _), 0) | (Self::TwoVars(_, x), 1) => (*x, ArrayVec::new()),
      (Self::TwoVars(y, x), 2) | (Self::TwoVars(x, y), 3) => {
        (*x, [Term::Variable(*y), Term::Variable(*x)].into())
      }
      _ => unreachable!(),
    }
  }
}
