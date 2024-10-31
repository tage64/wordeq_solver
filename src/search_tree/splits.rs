use std::cmp;

use vec_list::ListPtr;

use super::SearchNode;
use crate::*;

/// Split kind for a node in the search tree.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum SplitKind {
  /// One variable equal to the empty string or a terminal followed by a fresh variable.
  ///
  /// The third argument denotes the side of the variable.
  EmptyOrTerminal(Variable, Terminal, Side),
  /// Two variables, one from LHS and one from RHS.
  ///
  /// First, the first argument should come from LHS and the second from RHS. After calling
  /// `self.decide_order`, the variable to pick first shall come first. `decide_order()` should
  /// only be called once.
  TwoVars(Variable, Variable),
}
use SplitKind::*;

/// Splits from a node in the search tree.
///
/// The splits are from one clause involving one or two variables and 0 or one terminals.
#[derive(Debug, Clone)]
pub struct Splits {
  pub kind: SplitKind,
  clause_ptr: ListPtr,
  /// Whether the two variables in the TwoVars kind should be taken in opposite order.
  reversed: bool,
  /// Whether we should try to set the entire side except the last term (which must be a variable)
  /// equal to the first term (which also must be a variable) on the other side.
  first_last_var_test: Option<Side>,
}

impl SplitKind {
  /// Generate splits from this split kind.
  pub fn create_splits(self, node: &SearchNode, clause_ptr: ListPtr) -> Splits {
    /* TODO: This is too slow.
      let reversed = match &self {
        EmptyOrTerminal(_, _, _) => false,
        TwoVars(x, y) => {
          // Check if x or y is most common.
          let x_diff = node.var_ptrs[x.id]
            .iter()
            .map(|(clause_id, (x_in_lhs, x_in_rhs))| {
              let Clause {
                equation: Equation { lhs, rhs },
              } = node.formula.0.get(ListPtr::from_usize(clause_id));
              x_in_lhs.len() as isize - x_in_rhs.len() as isize + guess_word_len(rhs) as isize
                - guess_word_len(lhs) as isize
            })
            .sum::<isize>();
          let y_diff = node.var_ptrs[y.id]
            .iter()
            .map(|(clause_id, (y_in_lhs, y_in_rhs))| {
              let Clause {
                equation: Equation { lhs, rhs },
              } = node.formula.0.get(ListPtr::from_usize(clause_id));
              y_in_rhs.len() as isize - y_in_lhs.len() as isize + guess_word_len(lhs) as isize
                - guess_word_len(rhs) as isize
            })
            .sum::<isize>();
          x_diff >= y_diff
        }
      };
    */
    let reversed = false;
    let first_last_var_test = match &self {
      EmptyOrTerminal(x, _, side) => {
        if is_first_last_var_test(node, clause_ptr, *x, *side) {
          Some(*side)
        } else {
          None
        }
      }
      TwoVars(x, y) => {
        if is_first_last_var_test(node, clause_ptr, *x, Lhs) {
          Some(Lhs)
        } else if is_first_last_var_test(node, clause_ptr, *y, Rhs) {
          Some(Rhs)
        } else {
          None
        }
      }
    };
    Splits {
      kind: self,
      clause_ptr,
      reversed,
      first_last_var_test,
    }
  }
}

impl Splits {
  /// The number of splits (1..=5).
  pub fn len(&self) -> u32 {
    match &self.kind {
      EmptyOrTerminal(_, a, _) => cmp::min(
        AtomicBitSet::MAX,
        a.0.len() as u32
          + 1
          + if self.first_last_var_test.is_some() {
            1
          } else {
            0
          },
      ),
      TwoVars(_, _) => {
        4 + if self.first_last_var_test.is_some() {
          1
        } else {
          0
        }
      }
    }
  }

  /// Given a branch index, check whether the split will be a reducing split or not.
  pub fn is_reducing(&self, mut n: u32, solver: &SearchNode) -> bool {
    if self.first_last_var_test.is_some() {
      if n == 0 {
        return true;
      }
      n -= 1;
    }
    match (&self.kind, n) {
      (EmptyOrTerminal(_, _, _), 0) | (TwoVars(_, _), 0 | 1) => true,
      (EmptyOrTerminal(x, _, _), 1..) => {
        solver.var_ptrs[x.id].len() <= 1 && {
          let (lhs, rhs) = solver.var_ptrs[x.id].values().next().unwrap();
          lhs.len() + rhs.len() <= 1
        }
      }
      (TwoVars(_, _), 2) | (TwoVars(_, _), 3) => false,
      _ => unreachable!(),
    }
  }

  /// Get the nth split as a tuple (var, replacement).
  ///
  /// `n` the index of the branch.
  ///
  /// Returns a `(variable, assignment)` pair where `variable` is the variable to be
  /// assigned and `assignment` is the terms to assign to the variable.
  pub fn fix_var(&self, node: &mut SearchNode, mut n: u32) {
    if let Some(side) = self.first_last_var_test {
      if n == 0 {
        let other_side = node
          .formula
          .0
          .get(self.clause_ptr)
          .equation
          .side(side.opposite())
          .clone();
        let replacement = other_side
          .0
          .iter()
          .map(|(_, x)| x.clone())
          .take(other_side.0.len() - 1);
        debug_assert!(matches!(
          other_side.0.get(other_side.0.back().unwrap()),
          Term::Variable(_)
        ));
        let ((EmptyOrTerminal(x, _, _), _) | (TwoVars(x, _), Lhs) | (TwoVars(_, x), Rhs)) =
          (&self.kind, side);
        node.fix_var(*x, replacement);
        return;
      } else {
        n -= 1;
      }
    }
    match (&self.kind, n) {
      (EmptyOrTerminal(x, _, _), 0) => node.fix_var(*x, []),
      (EmptyOrTerminal(x, a, _), n) => {
        // TODO: Try to remove cloning.
        if n < self.len() - 1 {
          node.fix_var(*x, [Term::Terminal(Terminal(a.0[..n as usize].into()))])
        } else {
          node.fix_var(*x, [
            Term::Terminal(Terminal(a.0[..n as usize].into())),
            Term::Variable(*x),
          ])
        }
      }
      (TwoVars(x, _), 0) | (TwoVars(_, x), 1) => node.fix_var(*x, []),
      (TwoVars(y, x), 2) | (TwoVars(x, y), 3) => {
        let (x, y) = if self.reversed { (y, x) } else { (x, y) };
        node.fix_var(*x, [Term::Variable(*y), Term::Variable(*x)])
      }
      _ => unreachable!(),
    }
  }
}

/// Given a word, estimate the length of the word by counting all characters and counting variables
/// as one character.
#[expect(dead_code)]
fn guess_word_len(word: &Word) -> usize {
  word
    .0
    .iter()
    .map(|(_, t)| {
      if let Term::Terminal(s) = t {
        s.0.len()
      } else {
        1
      }
    })
    .sum()
}

/// Check if the variable occurs only once and that another variable occurs only once as last term
/// in the other side of the clause.
fn is_first_last_var_test(
  node: &SearchNode,
  clause_ptr: ListPtr,
  var: Variable,
  side: Side,
) -> bool {
  let Clause {
    equation: Equation { lhs, rhs },
  } = &node.formula.0.get(clause_ptr);
  let other_side = match side {
    Lhs => rhs,
    Rhs => lhs,
  };
  let Term::Variable(other_side_last_var) = other_side.0.get(other_side.0.back().unwrap()) else {
    return false;
  };
  var_only_on_one_side(node, clause_ptr, var, side).is_some_and(|occurences_1| {
    var_only_on_one_side(node, clause_ptr, *other_side_last_var, side.opposite())
      .is_some_and(|occurences_2| occurences_1 < 2 || occurences_2 < 2)
  })
}

/// Check if a variable exists only on one side in a given equation in the entire formula. Returns
/// the number of occurences in that side. If it occurs anywhere else in the formula None will be
/// returned.
#[inline]
fn var_only_on_one_side(
  node: &SearchNode,
  clause_ptr: ListPtr,
  var: Variable,
  side: Side,
) -> Option<usize> {
  let var_ptrs_for_clauses = &node.var_ptrs[var.id];
  if var_ptrs_for_clauses.len() == 1 {
    let (lhs_ptrs, rhs_ptrs) = &var_ptrs_for_clauses[clause_ptr.to_usize()];
    let (var_ptrs_same_side, var_ptrs_other_side) = match side {
      Lhs => (lhs_ptrs, rhs_ptrs),
      Rhs => (rhs_ptrs, lhs_ptrs),
    };
    if var_ptrs_other_side.is_empty() {
      return Some(var_ptrs_same_side.len());
    }
  }
  None
}
