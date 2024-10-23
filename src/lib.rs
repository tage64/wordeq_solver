pub mod benchmarks;
mod format_duration;
mod formula;
mod node_watcher;
pub mod vec_list;
use std::cell::{OnceCell, RefCell};
use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use arrayvec::ArrayVec;
use bit_set::BitSet;
use compact_str::CompactString;
use derive_more::Display;
pub use format_duration::format_duration;
pub use formula::*;
pub use node_watcher::*;
#[expect(unused_imports)]
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use vec_list::{Entry, ListPtr};
use vec_map::VecMap;

const INITIAL_MAX_DEPTH: usize = 4;
const MAX_DEPTH_STEP: usize = 2;

#[derive(Debug, Display, Serialize, Deserialize)]
pub enum Solution {
  #[display("SAT")]
  Sat(SatResult),
  #[display("UNSAT")]
  Unsat,
  Cancelled,
}
pub use Solution::*;

/// Simple solve function which doesn't use a watcher.
pub fn solve_no_watch(formula: Formula) -> Solution {
  solve(formula, dummy_watcher()).0
}

/// Try to solve a formula.
///
/// Takes in a closure (node_watcher) which may cancel the search at any node by returning
/// `ControlFlow::Break(_)`. It will be called at every new node, right before the fix point
/// function.
pub fn solve<W: NodeWatcher>(formula: Formula, mut node_watcher: W) -> (Solution, W) {
  let mut solver = SearchNode::new(formula.cnf.clone(), formula.var_names.len());
  /*let thread_pool = rayon::ThreadPoolBuilder::new()
  .stack_size(100000000)
  .build()
  .unwrap();*/
  let restart_node = solver.clone();
  let mut non_reducing_max_depth = INITIAL_MAX_DEPTH;
  loop {
    match solve_rec(
      solver,
      &formula,
      &mut node_watcher,
      non_reducing_max_depth,
      Arc::new(AtomicBool::new(false)),
    ) {
      FoundSolution(x) => return (x, node_watcher),
      UnsatBranch => return (Unsat, node_watcher),
      CancelledSearch => unreachable!(),
      ReachedMaxDepth => (),
    }
    non_reducing_max_depth += MAX_DEPTH_STEP;
    solver = restart_node.clone();
    log::trace!("Increasing max depth to {}", non_reducing_max_depth);
  }
}

/// An edge in the search tree.
#[derive(Debug)]
struct SearchEdge {
  parent: SearchNode,
  branches: Branches,
  branch_idx: usize,
}

fn solve_rec<W: NodeWatcher>(
  mut node: SearchNode,
  original_formula: &Formula,
  node_watcher: &W,
  non_reducing_max_depth: usize,
  should_exit_search: Arc<AtomicBool>,
) -> BranchResult {
  let mut parent_edges = Vec::<SearchEdge>::new();
  let mut branch_result = UnsatBranch;
  loop {
    if should_exit_search.load(Ordering::Acquire) {
      return CancelledSearch;
    }
    if node_watcher.visit_node(&node).is_break() {
      should_exit_search.store(true, Ordering::Release);
      return FoundSolution(Cancelled);
    }
    #[cfg(feature = "trace_logging")]
    log::trace!(
      "{:depth$}Solving formula: {}",
      "",
      node.formula.display(|x| &original_formula.var_names[x.id]),
      depth = node.depth,
    );
    node.assert_invariants();
    // Run the fix point function.
    let fix_point_res = node.fix_point();
    #[cfg(feature = "trace_logging")]
    log::trace!(
      "{:depth$}After fix_point(): {}",
      "",
      node.formula.display(|x| &original_formula.var_names[x.id]),
      depth = node.depth,
    );
    if let Err(()) = fix_point_res {
      // This branch is unsat.
      #[cfg(feature = "trace_logging")]
      log::trace!("{:1$}Unsatisfiable branch;", "", node.depth);
      parent_edges.last_mut().map(|x| x.branch_idx += 1);
      // TODO: Maybe do something with the branch result.
    } else {
      // Perform a split.
      let Some((branches, clause_ptr)) = node.splits.pop_first() else {
        // There are no splits so we've reached SAT!
        #[cfg(feature = "trace_logging")]
        log::trace!("SAT");
        should_exit_search.store(true, Ordering::Release);
        return FoundSolution(Sat(SatResult::new(original_formula.clone(), node)));
      };
      let branches = branches.decide_order(&node);
      node.splits_for_clause.remove(clause_ptr.to_usize());
      #[cfg(feature = "trace_logging")]
      log::trace!("{:depth$}New split;", "", depth = node.depth);
      parent_edges.push(SearchEdge {
        parent: node,
        branches,
        branch_idx: 0,
      });
    }
    loop {
      let Some(SearchEdge {
        parent,
        branches,
        branch_idx,
      }) = parent_edges.last_mut()
      else {
        return branch_result;
      };
      if *branch_idx == branches.len() {
        parent_edges.pop();
        parent_edges.last_mut().map(|x| x.branch_idx += 1);
        continue;
      }
      let non_reducing_depth = if !branches.is_reducing(*branch_idx, parent) {
        if parent.non_reducing_depth + 1 == non_reducing_max_depth {
          #[cfg(feature = "trace_logging")]
          log::trace!(
            "{:depth$}Max depth {} reached with this non reducing branch.",
            "",
            non_reducing_max_depth,
            depth = parent.depth + 1,
          );
          branch_result = ReachedMaxDepth;
          *branch_idx += 1;
          continue;
        }
        parent.non_reducing_depth + 1
      } else {
        parent.non_reducing_depth
      };
      node = parent.clone();
      node.depth += 1;
      node.non_reducing_depth = non_reducing_depth;
      let (branch_var, replacement) = branches.get(*branch_idx);
      #[cfg(feature = "trace_logging")]
      log::trace!(
        "{:depth$}branching: {} = {}",
        "",
        &original_formula.var_names[branch_var.id],
        display_word(replacement.iter(), |x| &original_formula.var_names[x.id]),
        depth = node.depth,
      );
      node.fix_var(branch_var, replacement);
      break;
    }
  }
}

/// A result of a branch in the search tree.
#[derive(Debug)]
enum BranchResult {
  /// A solution was found.
  FoundSolution(Solution),
  /// This branch is UNSAT.
  UnsatBranch,
  /// We reached max depth and found no solution.
  ReachedMaxDepth,
  /// Some thread set the `should_cancel_search` flag to true.
  CancelledSearch,
}
use BranchResult::*;

/// A result returned from the simplify_clause function.
#[derive(Debug, Clone)]
#[must_use]
enum SimplificationResult {
  /// Both LHS and RHS are empty.
  BothSidesEmpty,
  /// Unit propagation.
  UnitProp(UnitProp),
  /// Split on a variable at the start of LHS or RHS.
  Split(Branches),
}

/// Describe if unit propagation happens at the LHS or RHS.
#[derive(Debug, Clone, Copy)]
#[must_use]
enum UnitProp {
  /// LHS consists of one single variable and RHS is not empty.
  UnitPropLhs(Variable),
  /// RHS consists of one single variable and LHS is not empty.
  UnitPropRhs(Variable),
  /// LHS is empty.
  UnitPropEmptyLhs,
  /// RHS is empty.
  UnitPropEmptyRhs,
}
use UnitProp::*;

/// Branches for a clause involving one or two variables and 0 or one terminals.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Branches {
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

impl Branches {
  /// The number of splits (1..=5).
  fn len(&self) -> usize {
    match self {
      Self::Empty(_) => 1,
      Self::EmptyOrTerminal(_, _) => 2,
      Self::TwoVars(_, _) => 4,
    }
  }

  /// Given a branch index, check whether the branch will be a reducing branch or not.
  fn is_reducing(&self, n: usize, solver: &SearchNode) -> bool {
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
  fn decide_order(self, solver: &SearchNode) -> Self {
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
  fn get(&self, n: usize) -> (Variable, ArrayVec<Term, 2>) {
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

#[derive(Debug, Clone)]
pub struct SearchNode {
  /// The formula to solve. Clauses may be removed or modified but new clauses will never be added.
  formula: Cnf,
  /// The number of variables. Maybe sparse, that is, some of the previously used variables might
  /// have been fixed but they still count.
  no_vars: usize,
  /// assignments[x] = the value for variable with id x in the original formula.
  ///
  /// Note that the variable ids in the keys of this map corresponds to the variables in the
  /// original formula, while the variable ids in the values of this map as well as the variable
  /// ids in other parts of the solver changes over time. More specifically, if for instance the
  /// variable X gets assigned the value YX' where X' is a fresh variable, X' will reuse the id for
  /// X in all parts of the solver except the keys in this map.
  assignments: VecMap<Word>,
  /// assignments_var_ptrs[x][y] = a bitset for occurences of the variable x in the original
  /// variable y.
  assignments_var_ptrs: VecMap<VecMap<BitSet>>,
  /// var_ptrs is a map with variable ids as keys, the values are maps of all clauses where that
  /// variable exists, they have clause pointers as keys and pairs (lhs_ptrs, rhs_ptrs) as
  /// values, where lhs_ptrs and rhs_ptrs are bitsets of pointers to
  /// variables in the LHS and RHS of that clause equation respectively.
  var_ptrs: VecMap<VecMap<(BitSet, BitSet)>>,
  /// A set of pointers to all clauses which might have changed and should be checked.
  updated_clauses: BitSet,
  /// Splits is an ordered map with Branches as keys and clause indices as values.
  splits: BTreeMap<Branches, ListPtr>,
  /// splits[c] = the splits for clause c.
  splits_for_clause: VecMap<Branches>,
  /// The number of nodes above this node in the search tree.
  depth: usize,
  /// The number of non reducing edges above this node in the search tree.
  non_reducing_depth: usize,
}

impl SearchNode {
  fn new(formula: Cnf, no_vars: usize) -> Self {
    let mut var_ptrs = VecMap::with_capacity(no_vars);
    for (clause_ptr, clause) in formula.0.iter() {
      for (term_ptr, term) in clause.equation.lhs.0.iter() {
        if let Term::Variable(var) = term {
          var_ptrs
            .entry(var.id)
            .or_insert_with(VecMap::new)
            .entry(clause_ptr.to_usize())
            .or_insert((BitSet::new(), BitSet::new()))
            .0
            .insert(term_ptr.to_usize());
        }
      }
      for (term_ptr, term) in clause.equation.rhs.0.iter() {
        if let Term::Variable(var) = term {
          var_ptrs
            .entry(var.id)
            .or_insert_with(VecMap::new)
            .entry(clause_ptr.to_usize())
            .or_insert((BitSet::new(), BitSet::new()))
            .1
            .insert(term_ptr.to_usize());
        }
      }
    }
    let updated_clauses = formula.0.iter().map(|(ptr, _)| ptr.to_usize()).collect();
    Self {
      formula,
      no_vars,
      assignments: VecMap::new(),
      assignments_var_ptrs: VecMap::new(),
      var_ptrs,
      updated_clauses,
      splits: BTreeMap::new(),
      splits_for_clause: VecMap::new(),
      depth: 0,
      non_reducing_depth: 0,
    }
  }

  #[cfg(debug_assertions)]
  fn assert_invariants(&self) {
    // Assert invariants related to self.var_ptrs and self.assignments.
    // Check that self.var_ptrs is sound.
    for var in (0..self.no_vars).map(|id| Variable { id }) {
      if self.var_ptrs.contains_key(var.id) {
        // Check that all pointers actually point to terms with var.
        for (clause_id, (lhs_ptrs, rhs_ptrs)) in &self.var_ptrs[var.id] {
          assert!(!lhs_ptrs.is_empty() || !rhs_ptrs.is_empty());
          let clause_ptr = ListPtr::from_usize(clause_id);
          let Clause {
            equation: Equation { lhs, rhs },
          } = self.formula.0.get(clause_ptr);
          for var_ptr in lhs_ptrs.iter().map(ListPtr::from_usize) {
            assert_eq!(*lhs.0.get(var_ptr), Term::Variable(var));
          }
          for var_ptr in rhs_ptrs.iter().map(ListPtr::from_usize) {
            assert_eq!(*rhs.0.get(var_ptr), Term::Variable(var));
          }
        }
      }
    }
    // Check that self.var_ptrs is complete. That is, it contains **all** occurences of a variable.
    for (clause_ptr, clause) in self.formula.0.iter() {
      // Check that self.splits is a subset of self.splits_for_clause.
      if let Some(branches) = self.splits_for_clause.get(clause_ptr.to_usize()) {
        assert_eq!(self.splits[branches], clause_ptr);
      }
      assert!(
        !(self.updated_clauses.contains(clause_ptr.to_usize())
          && self.splits_for_clause.contains_key(clause_ptr.to_usize())),
        "self.updated_clauses and self.splits_for_clause must be disjunct."
      );
      for (term_ptr, term) in clause.equation.lhs.0.iter() {
        if let Term::Variable(var) = term {
          assert!(
            self
              .var_ptrs
              .get(var.id)
              .unwrap()
              .get(clause_ptr.to_usize())
              .unwrap()
              .0
              .contains(term_ptr.to_usize())
          );
        }
      }
      for (term_ptr, term) in clause.equation.rhs.0.iter() {
        if let Term::Variable(var) = term {
          assert!(
            self
              .var_ptrs
              .get(var.id)
              .unwrap()
              .get(clause_ptr.to_usize())
              .unwrap()
              .1
              .contains(term_ptr.to_usize())
          );
        }
      }
    }

    // Check that self.assignments and self.assignments_var_ptrs are consistent with each other.
    for (var_id, assignment) in self.assignments.iter() {
      for (ptr, term) in assignment.0.iter() {
        if let Term::Variable(x) = term {
          assert!(self.assignments_var_ptrs[x.id][var_id].contains(ptr.to_usize()));
        }
      }
    }
    for (var_id, var_ptrs) in self.assignments_var_ptrs.iter() {
      assert!(!var_ptrs.is_empty(), "empty maps should not exist.");
      for (orig_var_id, ptrs) in var_ptrs.iter() {
        for ptr in ptrs.iter().map(ListPtr::from_usize) {
          assert_eq!(
            &Term::Variable(Variable { id: var_id }),
            self.assignments[orig_var_id].0.get(ptr)
          );
        }
      }
    }

    // Check that self.updated_clauses point to valid clauses.
    self
      .updated_clauses
      .iter()
      .for_each(|x| assert!(self.formula.0.contains_ptr(ListPtr::from_usize(x))));
    // Check that self.splits_for_clause is a subset of self.splits.
    for (branches, clause_ptr) in self.splits.iter() {
      assert_eq!(&self.splits_for_clause[clause_ptr.to_usize()], branches);
    }
  }
  #[cfg(not(debug_assertions))]
  fn assert_invariants(&self) {}

  /// In a loop: Simplify the equations and perform unit propagation. Return Err(()) on unsat.
  fn fix_point(&mut self) -> Result<(), ()> {
    while !self.updated_clauses.is_empty() {
      let mut unit_propagations = Vec::new();
      while let Some(clause_ptr) = self.updated_clauses.iter().next().map(ListPtr::from_usize) {
        self.updated_clauses.remove(clause_ptr.to_usize());
        match self.simplify_equation(clause_ptr)? {
          SimplificationResult::BothSidesEmpty => {
            self.remove_clause(clause_ptr);
          }
          SimplificationResult::UnitProp(x) => unit_propagations.push((clause_ptr, x)),
          SimplificationResult::Split(branches) => {
            if let Some(prev_clause) = self.splits.insert(branches.clone(), clause_ptr) {
              self.splits_for_clause.remove(prev_clause.to_usize());
            }
            self
              .splits_for_clause
              .insert(clause_ptr.to_usize(), branches);
          }
        }
      }

      // Perform unit propagations.
      for (clause_ptr, unit_prop) in unit_propagations {
        if self.updated_clauses.contains(clause_ptr.to_usize()) {
          continue;
        }
        self.assert_invariants();
        let Clause {
          equation: Equation { lhs, rhs },
        } = self.formula.0.get(clause_ptr);
        match unit_prop {
          UnitPropEmptyLhs => {
            let mut to_be_empty = BitSet::new(); // All variables in RHS.
            for (_, term) in rhs.0.iter() {
              match *term {
                Term::Terminal(_) => return Err(()),
                Term::Variable(x) => {
                  to_be_empty.insert(x.id);
                }
              }
            }
            for x in to_be_empty.iter() {
              self.fix_var(Variable { id: x }, []);
            }
          }
          UnitPropEmptyRhs => {
            let mut to_be_empty = BitSet::new(); // All variables in LHS.
            for (_, term) in lhs.0.iter() {
              match *term {
                Term::Terminal(_) => return Err(()),
                Term::Variable(x) => {
                  to_be_empty.insert(x.id);
                }
              }
            }
            for x in to_be_empty.iter() {
              self.fix_var(Variable { id: x }, []);
            }
          }
          UnitPropLhs(var) => {
            // Check if RHS contains var.
            if self.var_ptrs[var.id][clause_ptr.to_usize()].1.is_empty() {
              // RHS does not contain var.
              self.fix_var(var, rhs.clone().0.iter().map(|(_, x)| *x));
            } else {
              // Set everything in RHS but var to be empty.
              let mut var_occurences = 0; // Count occurences of var in RHS.
              let mut to_be_empty = BitSet::new(); // All variables in RHS which are not var.
              for (_, term) in rhs.0.iter() {
                match *term {
                  Term::Terminal(_) => return Err(()),
                  Term::Variable(x) => {
                    if x == var {
                      var_occurences += 1;
                    } else {
                      to_be_empty.insert(x.id);
                    }
                  }
                }
              }
              if var_occurences != 1 {
                to_be_empty.insert(var.id);
              }
              for x in to_be_empty.iter() {
                self.fix_var(Variable { id: x }, []);
              }
            }
          }
          UnitPropRhs(var) => {
            // Check if LHS contains var.
            if self.var_ptrs[var.id][clause_ptr.to_usize()].0.is_empty() {
              // LHS does not contain var.
              self.fix_var(var, lhs.clone().0.iter().map(|(_, x)| *x));
            } else {
              // Set everything in LHS but var to be empty.
              let mut var_occurences = 0; // Count occurences of var in LHS.
              let mut to_be_empty = BitSet::new(); // All variables in LHS which are not var.
              for (_, term) in lhs.0.iter() {
                match *term {
                  Term::Terminal(_) => return Err(()),
                  Term::Variable(x) => {
                    if x == var {
                      var_occurences += 1;
                    } else {
                      to_be_empty.insert(x.id);
                    }
                  }
                }
              }
              if var_occurences != 1 {
                to_be_empty.insert(var.id);
              }
              for x in to_be_empty.iter() {
                self.fix_var(Variable { id: x }, []);
              }
            }
          }
        }
        // The clause is true so let's remove it.
        self.remove_clause(clause_ptr);
      }
      self.assert_invariants();
    }
    Ok(())
  }

  /// Simplify an equation as much as possible. Return Err(()) on unsat.
  fn simplify_equation(&mut self, clause_ptr: ListPtr) -> Result<SimplificationResult, ()> {
    use SimplificationResult::*;
    let Clause {
      equation: Equation { lhs, rhs },
    } = self.formula.0.get_mut(clause_ptr);
    // Remove equal terminals from the end.
    loop {
      let lhs_back_ptr = lhs.0.back();
      let rhs_back_ptr = rhs.0.back();
      let lhs_back = lhs_back_ptr.map(|x| *lhs.0.get(x));
      let rhs_back = rhs_back_ptr.map(|x| *rhs.0.get(x));
      match (lhs_back, rhs_back) {
        (None, None) => return Ok(BothSidesEmpty),
        (None, Some(Term::Variable(_))) => {
          if let Term::Terminal(_) = rhs.0.get(rhs.0.head().unwrap()) {
            return Err(());
          } else {
            // LHS is empty and RHS is empty or starts and ends with variables.
            return Ok(UnitProp(UnitPropEmptyLhs));
          }
        }
        (Some(Term::Variable(_)), None) => {
          if let Term::Terminal(_) = lhs.0.get(lhs.0.head().unwrap()) {
            return Err(());
          } else {
            // RHS is empty and LHS starts and ends with variables.
            return Ok(UnitProp(UnitPropEmptyRhs));
          }
        }
        (None, Some(Term::Terminal(_))) | (Some(Term::Terminal(_)), None) => return Err(()),
        (Some(x), Some(y)) if x == y => {
          // Both sides ends with the same terminal or variable.
          lhs.0.remove(lhs_back_ptr.unwrap());
          rhs.0.remove(rhs_back_ptr.unwrap());
          // Check if we should remove from self.var_ptrs.
          if let Term::Variable(x) = x {
            // We removed the variable x at both LHS and RHS.
            let vec_map::Entry::Occupied(mut entry) =
              self.var_ptrs[x.id].entry(clause_ptr.to_usize())
            else {
              unreachable!()
            };
            entry.get_mut().0.remove(lhs_back_ptr.unwrap().to_usize());
            entry.get_mut().1.remove(rhs_back_ptr.unwrap().to_usize());
            if entry.get().0.is_empty() && entry.get().1.is_empty() {
              entry.remove();
            }
            if self.var_ptrs[x.id].is_empty() {
              self.var_ptrs.remove(x.id);
            }
          }
        }
        // Rule 6: Both sides end with distinct terminals:
        (Some(Term::Terminal(_)), Some(Term::Terminal(_))) => {
          return Err(());
        }
        (Some(Term::Variable(_)), Some(_)) | (Some(_), Some(Term::Variable(_))) => break,
      }
    }
    // Remove equal terminals from the start and perform split.
    loop {
      let lhs_head_ptr = lhs.0.head();
      let rhs_head_ptr = rhs.0.head();
      let lhs_head = lhs_head_ptr.map(|x| *lhs.0.get(x));
      let rhs_head = rhs_head_ptr.map(|x| *rhs.0.get(x));
      match (lhs_head, rhs_head) {
        (None, None) => return Ok(BothSidesEmpty),
        (None, Some(Term::Variable(_))) => {
          if let Term::Terminal(_) = rhs.0.get(rhs.0.head().unwrap()) {
            return Err(());
          } else {
            // LHS is empty and RHS is empty or starts and ends with variables.
            return Ok(UnitProp(UnitPropEmptyLhs));
          }
        }
        (Some(Term::Variable(_)), None) => {
          if let Term::Terminal(_) = lhs.0.get(lhs.0.head().unwrap()) {
            return Err(());
          } else {
            // RHS is empty and LHS starts and ends with variables.
            return Ok(UnitProp(UnitPropEmptyRhs));
          }
        }
        (None, Some(Term::Terminal(_))) | (Some(Term::Terminal(_)), None) => return Err(()),
        (Some(x), Some(y)) if x == y => {
          // Both sides starts with the same terminal or variable.
          lhs.0.remove(lhs_head_ptr.unwrap());
          rhs.0.remove(rhs_head_ptr.unwrap());
          // Check if we should remove from self.var_ptrs.
          if let Term::Variable(x) = x {
            // We removed the variable x at both LHS and RHS.
            let vec_map::Entry::Occupied(mut entry) =
              self.var_ptrs[x.id].entry(clause_ptr.to_usize())
            else {
              unreachable!()
            };
            entry.get_mut().0.remove(lhs_head_ptr.unwrap().to_usize());
            entry.get_mut().1.remove(rhs_head_ptr.unwrap().to_usize());
            if entry.get().0.is_empty() && entry.get().1.is_empty() {
              entry.remove();
            }
            if self.var_ptrs[x.id].is_empty() {
              self.var_ptrs.remove(x.id);
            }
          }
        }
        // Rule 6: Both sides start with distinct terminals:
        (Some(Term::Terminal(_)), Some(Term::Terminal(_))) => {
          return Err(());
        }
        // Rule 7: One side starts with a terminal and the other starts with a variable.
        (Some(Term::Terminal(a)), Some(Term::Variable(x))) => {
          if rhs_head_ptr == rhs.0.back() {
            // RHS is a single variable.
            return Ok(UnitProp(UnitPropRhs(x)));
          } else {
            return Ok(Split(Branches::EmptyOrTerminal(x, a)));
          }
        }
        (Some(Term::Variable(x)), Some(Term::Terminal(a))) => {
          if lhs_head_ptr == lhs.0.back() {
            // LHS is a single variable.
            return Ok(UnitProp(UnitPropLhs(x)));
          } else {
            return Ok(Split(Branches::EmptyOrTerminal(x, a)));
          }
        }
        // Rule 8: Both sides starts with variables.
        (Some(Term::Variable(x)), Some(Term::Variable(y))) => {
          if lhs_head_ptr == lhs.0.back() {
            // LHS is a single variable.
            return Ok(UnitProp(UnitPropLhs(x)));
          } else if rhs_head_ptr == rhs.0.back() {
            // RHS is a single variable.
            return Ok(UnitProp(UnitPropRhs(y)));
          } else {
            return Ok(Split(Branches::TwoVars(x, y)));
          }
        }
      };
    }
  }

  /// Remove a clause.
  fn remove_clause(&mut self, clause_ptr: ListPtr) {
    // We will not get any ABA problems because we should only remove not add clauses.
    let Clause {
      equation: Equation { lhs, rhs },
    } = self.formula.0.remove(clause_ptr);
    // Remove all variable pointers from self.var_ptrs.
    for (_, term) in lhs.0.iter() {
      if let Term::Variable(var) = term {
        if let vec_map::Entry::Occupied(mut entry) = self.var_ptrs.entry(var.id) {
          entry.get_mut().remove(clause_ptr.to_usize());
          if entry.get().is_empty() {
            entry.remove();
          }
        }
      }
    }
    for (_, term) in rhs.0.iter() {
      if let Term::Variable(var) = term {
        if let vec_map::Entry::Occupied(mut entry) = self.var_ptrs.entry(var.id) {
          entry.get_mut().remove(clause_ptr.to_usize());
          if entry.get().is_empty() {
            entry.remove();
          }
        }
      }
    }
    self.updated_clauses.remove(clause_ptr.to_usize());
    if let Some(branches) = self.splits_for_clause.remove(clause_ptr.to_usize()) {
      self.splits.remove(&branches);
    }
  }

  /// Given a variable and a value, replace all occurences of that variable with the value.
  fn fix_var(&mut self, var: Variable, val: impl IntoIterator<Item = Term> + Clone) {
    for (clause_id, (lhs_ptrs, rhs_ptrs)) in self.var_ptrs.remove(var.id).unwrap().iter() {
      self.updated_clauses.insert(clause_id);
      if let Some(branches) = self.splits_for_clause.remove(clause_id) {
        self.splits.remove(&branches);
      }
      let clause_ptr = ListPtr::from_usize(clause_id);
      let Clause {
        equation: Equation { lhs, rhs },
      } = self.formula.0.get_mut(clause_ptr);
      for term_ptr in lhs_ptrs.iter().map(ListPtr::from_usize) {
        for insert_term in val.clone() {
          let insert_ptr = lhs.0.insert_before(term_ptr, insert_term);
          if let Term::Variable(var) = insert_term {
            self
              .var_ptrs
              .entry(var.id)
              .or_insert_with(VecMap::new)
              .entry(clause_id)
              .or_insert((BitSet::new(), BitSet::new()))
              .0
              .insert(insert_ptr.to_usize());
          }
        }
        lhs.0.remove(term_ptr);
      }
      for term_ptr in rhs_ptrs.iter().map(ListPtr::from_usize) {
        for insert_term in val.clone() {
          let insert_ptr = rhs.0.insert_before(term_ptr, insert_term);
          if let Term::Variable(var) = insert_term {
            self
              .var_ptrs
              .entry(var.id)
              .or_insert_with(VecMap::new)
              .entry(clause_id)
              .or_insert((BitSet::new(), BitSet::new()))
              .1
              .insert(insert_ptr.to_usize());
          }
        }
        rhs.0.remove(term_ptr);
      }
    }
    if let Some(var_ptrs) = self.assignments_var_ptrs.remove(var.id) {
      for (orig_var_id, ptrs) in var_ptrs {
        let assignment = &mut self.assignments[orig_var_id];
        for term_ptr in ptrs.iter().map(ListPtr::from_usize) {
          for insert_term in val.clone() {
            let insert_ptr = assignment.0.insert_before(term_ptr, insert_term);
            if let Term::Variable(x) = insert_term {
              self
                .assignments_var_ptrs
                .entry(x.id)
                .or_insert_with(VecMap::new)
                .entry(orig_var_id)
                .or_insert_with(BitSet::new)
                .insert(insert_ptr.to_usize());
            }
          }
          assignment.0.remove(term_ptr);
        }
      }
    }
    if let vec_map::Entry::Vacant(entry) = self.assignments.entry(var.id) {
      let mut assignment = Word::default();
      for insert_term in val.clone() {
        let insert_ptr = assignment.0.insert_back(insert_term);
        if let Term::Variable(x) = insert_term {
          self
            .assignments_var_ptrs
            .entry(x.id)
            .or_insert_with(VecMap::new)
            .entry(var.id)
            .or_insert_with(BitSet::new)
            .insert(insert_ptr.to_usize());
        }
      }
      entry.insert(assignment);
    }
  }

  /// Get an approximated list of the fields in this struct together with their dynamic sizes.
  pub fn get_sizes(&self) -> [(&'static str, usize); 9] {
    [
      (
        "formula",
        size_of::<SearchNode>()
          + size_of::<Cnf>()
          + self
            .formula
            .0
            .iter()
            .map(|x| {
              size_of::<Entry<Clause>>()
                + size_of::<Entry<Term>>() * (x.1.equation.lhs.0.len() + x.1.equation.rhs.0.len())
            })
            .sum::<usize>(),
      ),
      ("no_vars", size_of::<usize>()),
      (
        "assignments",
        size_of::<VecMap<Word>>()
          + self.assignments.capacity() * size_of::<Option<Word>>()
          + self
            .assignments
            .values()
            .map(|x| x.0.len() * size_of::<Term>())
            .sum::<usize>(),
      ),
      (
        "assignments_var_ptrs",
        size_of::<VecMap<VecMap<BitSet>>>()
          + self.assignments_var_ptrs.capacity() * size_of::<VecMap<BitSet>>()
          + self
            .assignments_var_ptrs
            .values()
            .map(|x| {
              x.capacity() * size_of::<BitSet>()
                + x
                  .values()
                  .map(|ptrs| (ptrs.len() as f64 / 8.0).ceil() as usize)
                  .sum::<usize>()
            })
            .sum::<usize>(),
      ),
      (
        "var_ptrs",
        size_of::<VecMap<VecMap<(BitSet, BitSet)>>>()
          + self.var_ptrs.capacity() * size_of::<VecMap<(BitSet, BitSet)>>()
          + self
            .var_ptrs
            .values()
            .map(|x| {
              x.capacity() * size_of::<(BitSet, BitSet)>()
                + x
                  .values()
                  .map(|(lhs, rhs)| {
                    (lhs.len() as f64 / 8.0).ceil() as usize
                      + (rhs.len() as f64 / 8.0).ceil() as usize
                  })
                  .sum::<usize>()
            })
            .sum::<usize>(),
      ),
      (
        "updated_clauses",
        size_of::<BitSet>() + (self.updated_clauses.len() as f64 / 8.0).ceil() as usize,
      ),
      (
        "splits",
        size_of::<BTreeMap<Branches, ListPtr>>()
          + self.splits.len() * (size_of::<Branches>() + size_of::<ListPtr>()),
      ),
      (
        "splits_for_clause",
        size_of::<VecMap<Branches>>() + self.splits_for_clause.capacity() * size_of::<Branches>(),
      ),
      ("last_static_items", size_of::<usize>() + size_of::<usize>()),
    ]
  }
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

impl SatResult {
  fn new(original_formula: Formula, solver: SearchNode) -> Self {
    Self {
      formula: original_formula,
      assignments: solver.assignments,
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
          match *term {
            Term::Terminal(Terminal(c)) => substituted_lhs.push(c),
            Term::Variable(var) => substituted_lhs += &self.get_var(var),
          }
        }
        let mut substituted_rhs = CompactString::default();
        for (_, term) in clause.equation.rhs.0.iter() {
          match *term {
            Term::Terminal(Terminal(c)) => substituted_rhs.push(c),
            Term::Variable(var) => substituted_rhs += &self.get_var(var),
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
          if let Term::Terminal(Terminal(c)) = *term {
            Some(c)
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
