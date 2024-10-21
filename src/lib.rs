mod format_duration;
mod formula;
mod node_watcher;
pub mod vec_list;
use std::cell::RefCell;
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
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
#[cfg(feature = "trace_logging")]
use vec_list::Entry;
use vec_list::ListPtr;
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

/// Try to solve a formula.
///
/// Takes in a closure (node_watcher) which may cancel the search at any node by returning
/// `ControlFlow::Break(_)`. It will be called at every new node, right before the fix point
/// function.
pub fn solve<W: NodeWatcher>(formula: Formula, node_watcher: W) -> (Solution, W) {
  Solver::new(formula.cnf, formula.var_names).solve(node_watcher)
}

/// Simple solve function which doesn't use a watcher.
pub fn solve_no_watch(formula: Formula) -> Solution {
  solve(formula, dummy_watcher()).0
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
  fn is_reducing(&self, n: usize, solver: &Solver) -> bool {
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
  fn decide_order(self, solver: &Solver) -> Self {
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
  fn get(&self, n: usize, solver: &mut Solver) -> (Variable, ArrayVec<Term, 2>) {
    match (self, n) {
      (Self::Empty(x), 0) | (Self::EmptyOrTerminal(x, _), 0) => (*x, ArrayVec::new()),
      (Self::EmptyOrTerminal(x, a), 1) => (
        *x,
        [Term::Terminal(*a), Term::Variable(solver.add_fresh_var(*x))].into(),
      ),
      (Self::TwoVars(x, _), 0) | (Self::TwoVars(_, x), 1) => (*x, ArrayVec::new()),
      (Self::TwoVars(y, x), 2) | (Self::TwoVars(x, y), 3) => (
        *x,
        [Term::Variable(*y), Term::Variable(solver.add_fresh_var(*x))].into(),
      ),
      _ => unreachable!(),
    }
  }
}

#[derive(Debug, Clone)]
pub struct Solver {
  /// The formula to solve. Clauses may be removed or modified but new clauses will never be added.
  formula: Cnf,
  original_formula: Arc<Formula>,
  /// The number of variables. Maybe sparse, that is, some of the previously used variables might
  /// have been fixed but they still count.
  no_vars: usize,
  /// assignments[x] = the value for variable with id x.
  assignments: VecMap<Vec<Term>>,
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
  parent: Option<Arc<Solver>>,
  depth: usize,
  max_depth: usize,
  /// Set this to true when the search should exit.
  should_exit_search: Arc<AtomicBool>,

  #[cfg(feature = "trace_logging")]
  /// var_names[x] = the name for variable with id x.
  var_names: Vec<CompactString>,
  #[cfg(feature = "trace_logging")]
  /// The actual depth including reducing nodes.
  actual_depth: usize,
}

impl Solver {
  fn new(formula: Cnf, var_names: Vec<CompactString>) -> Self {
    let no_vars = var_names.len();
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
      #[cfg(feature = "trace_logging")]
      var_names: var_names.clone(),
      #[cfg(feature = "trace_logging")]
      actual_depth: 0,
      original_formula: Arc::new(Formula::new(formula.clone(), var_names)),
      formula,
      no_vars,
      assignments: VecMap::new(),
      var_ptrs,
      updated_clauses,
      splits: BTreeMap::new(),
      splits_for_clause: VecMap::new(),
      parent: None,
      depth: 0,
      max_depth: INITIAL_MAX_DEPTH,
      should_exit_search: Arc::new(AtomicBool::new(false)),
    }
  }

  #[cfg(debug_assertions)]
  fn assert_invariants(&self) {
    // Assert invariants related to self.var_ptrs and self.assignments.
    #[cfg(feature = "trace_logging")]
    assert_eq!(self.no_vars, self.var_names.len());
    // Check that self.var_ptrs is sound.
    for var in (0..self.no_vars).map(|id| Variable { id }) {
      assert!(
        !(self.assignments.contains_key(var.id) && self.var_ptrs.contains_key(var.id)),
        "self.assignments and self.var_ptrs should be disjunct."
      );
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

    // Check that self.updated_clauses point to valid clauses.
    self
      .updated_clauses
      .iter()
      .for_each(|x| assert!(self.formula.0.contains_ptr(ListPtr::from_usize(x))));
    // Check that self.splits_for_clause is a subset of self.splits.
    for (branches, clause_ptr) in self.splits.iter() {
      assert_eq!(&self.splits_for_clause[clause_ptr.to_usize()], branches);
    }

    // Check that the depth is correct.
    let mut solver = self;
    while let Some(parent) = &solver.parent {
      assert!(parent.depth + 1 == solver.depth || parent.depth == solver.depth);
      solver = &*parent;
    }
    assert_eq!(solver.depth, 0);
  }
  #[cfg(not(debug_assertions))]
  fn assert_invariants(&self) {}

  /// Solve the formula.
  ///
  /// Takes in a closure (node_watcher) which may cancel the search at any node by returning
  /// `ControlFlow::Break(_)`. It will be called at every new node, right before the fix point
  /// function.
  ///
  /// The `var_names` argument is moved into the `SatResult` when finished.
  fn solve<W: NodeWatcher>(mut self, mut node_watcher: W) -> (Solution, W) {
    let thread_pool = rayon::ThreadPoolBuilder::new()
      .stack_size(100000000)
      .build()
      .unwrap();
    let mut restart_node = self.clone();
    loop {
      match thread_pool.install(|| self.solve_rec(&mut node_watcher)) {
        FoundSolution(x) => return (x, node_watcher),
        UnsatBranch => return (Unsat, node_watcher),
        CancelledSearch => unreachable!(),
        ReachedMaxDepth => (),
      }
      restart_node.max_depth += MAX_DEPTH_STEP;
      self = restart_node.clone();
      log::trace!("Increasing max depth to {}", self.max_depth);
    }
  }

  fn solve_rec<W: NodeWatcher>(mut self, node_watcher: &W) -> BranchResult {
    if self.should_exit_search.load(Ordering::Acquire) {
      return CancelledSearch;
    }
    if node_watcher.visit_node(&self).is_break() {
      self.should_exit_search.store(true, Ordering::Release);
      return FoundSolution(Cancelled);
    }
    #[cfg(feature = "trace_logging")]
    log::trace!(
      "{:depth$}Solving formula: {}",
      "",
      self.formula.display(|x| &self.var_names[x.id]),
      depth = self.depth
    );
    self.assert_invariants();
    // Run the fix point function.
    let fix_point_res = self.fix_point();
    #[cfg(feature = "trace_logging")]
    log::trace!(
      "{:depth$}After fix_point(): {}",
      "",
      self.formula.display(|x| &self.var_names[x.id]),
      depth = self.depth
    );
    if let Err(()) = fix_point_res {
      // This branch is unsat.
      #[cfg(feature = "trace_logging")]
      log::trace!("{:1$}Unsatisfiable branch;", "", self.depth);
      return UnsatBranch;
    }
    // Perform a split.
    let Some((branches, clause_ptr)) = self.splits.pop_first() else {
      // There are no splits so we've reached SAT!
      #[cfg(feature = "trace_logging")]
      log::trace!("SAT");
      self.should_exit_search.store(true, Ordering::Release);
      return FoundSolution(Sat(SatResult::new(
        self.original_formula.as_ref().clone(),
        self,
      )));
    };
    let branches = branches.decide_order(&self);
    self.splits_for_clause.remove(clause_ptr.to_usize());
    #[cfg(feature = "trace_logging")]
    log::trace!("{:1$}New split;", "", self.depth);
    let self_ = Arc::new(self);
    (0..branches.len())
      .into_par_iter()
      .map(|i| {
        let depth = if !branches.is_reducing(i, &self_) {
          if self_.depth == self_.max_depth {
            #[cfg(feature = "trace_logging")]
            log::trace!(
              "{:2$}Max depth {} reached with this non reducing branch.",
              "",
              self_.max_depth,
              self_.depth,
            );
            return ReachedMaxDepth;
          }
          self_.depth + 1
        } else {
          self_.depth
        };
        let mut child = (*self_).clone();
        child.parent = Some(self_.clone());
        child.depth = depth;
        #[cfg(feature = "trace_logging")]
        {
          child.actual_depth = self_.actual_depth + 1;
        }
        let (branch_var, replacement) = branches.get(i, &mut child);
        #[cfg(feature = "trace_logging")]
        log::trace!(
          "{:3$}branching: {} = {}",
          "",
          &child.var_names[branch_var.id],
          display_word(replacement.iter(), |x| &child.var_names[x.id]),
          depth,
        );
        child.fix_var(branch_var, replacement);
        child.solve_rec(node_watcher)
      })
      .reduce_with(|x, y| match (x, y) {
        (UnsatBranch, UnsatBranch) => UnsatBranch,
        (x @ FoundSolution(_), _) | (_, x @ FoundSolution(_)) => x,
        (CancelledSearch, _) | (_, CancelledSearch) => CancelledSearch,
        (ReachedMaxDepth, _) | (_, ReachedMaxDepth) => ReachedMaxDepth,
      })
      .unwrap()
  }

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
    debug_assert!(
      val
        .clone()
        .into_iter()
        .find(|x| *x == Term::Variable(var))
        .is_none()
    );
    for (clause_id, (lhs_ptrs, rhs_ptrs)) in self.var_ptrs[var.id].clone().iter() {
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
    self.var_ptrs.remove(var.id);
    self.assignments.insert(var.id, val.into_iter().collect());
  }

  /// Add a fresh variable and increment self.no_vars.
  #[allow(unused_variables)]
  fn add_fresh_var(&mut self, from: Variable) -> Variable {
    let new_var = Variable { id: self.no_vars };
    self.no_vars += 1;
    #[cfg(feature = "trace_logging")]
    {
      let name = self.var_names[from.id].clone() + "'";
      self.var_names.push(name);
    }
    new_var
  }

  /// Get an approximated list of the fields in this struct together with their dynamic sizes.
  #[cfg(feature = "trace_logging")]
  pub fn get_sizes(&self) -> [(&'static str, usize); 9] {
    [
      (
        "formula",
        size_of::<Solver>()
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
      ("original_formula", size_of::<Arc<Formula>>()),
      ("no_vars", size_of::<usize>()),
      (
        "assignments",
        size_of::<VecMap<Vec<Term>>>()
          + self.assignments.capacity() * size_of::<Option<Vec<Term>>>()
          + self
            .assignments
            .values()
            .map(|x| x.capacity() * size_of::<Term>())
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
      (
        "last_static_items",
        size_of::<Option<Arc<Solver>>>()
          + size_of::<usize>()
          + size_of::<usize>()
          + size_of::<Arc<AtomicBool>>(),
      ),
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
  assignments: AssignedVars,
  /// The formula where all variables have been substituted to a satisfying solution.
  substituted_formula: Option<Vec<(CompactString, CompactString)>>,
}

impl SatResult {
  fn new(original_formula: Formula, solver: Solver) -> Self {
    Self {
      formula: original_formula,
      assignments: AssignedVars {
        assignments: solver.assignments,
        var_cache: VecMap::new(),
      },
      substituted_formula: None,
    }
  }

  /// Get all clauses ((LHS, RHS) pairs) where all variables have been replaced by terminals
  /// to form a satisfying solution.
  pub fn substituted_formula(&mut self) -> &Vec<(CompactString, CompactString)> {
    self.substituted_formula.get_or_insert_with(|| {
      let mut substituted_formula = Vec::new();
      for (_, clause) in self.formula.cnf.0.iter() {
        let mut substituted_lhs = CompactString::default();
        for (_, term) in clause.equation.lhs.0.iter() {
          match *term {
            Term::Terminal(Terminal(c)) => substituted_lhs.push(c),
            Term::Variable(var) => substituted_lhs += self.assignments.get_var(var),
          }
        }
        let mut substituted_rhs = CompactString::default();
        for (_, term) in clause.equation.rhs.0.iter() {
          match *term {
            Term::Terminal(Terminal(c)) => substituted_rhs.push(c),
            Term::Variable(var) => substituted_rhs += self.assignments.get_var(var),
          }
        }
        substituted_formula.push((substituted_lhs, substituted_rhs));
      }
      substituted_formula
    })
  }

  /// Get a value for a variable which contribute to a satisfying solution.
  pub fn get_var(&mut self, var: Variable) -> &str {
    self.assignments.get_var(var)
  }

  /// Check that the solution is correct.
  pub fn assert_correct(&mut self) {
    self.substituted_formula();
    for (lhs, rhs) in self.substituted_formula.as_ref().unwrap() {
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

/// Struct for holding and incrementally updating variables.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct AssignedVars {
  assignments: VecMap<Vec<Term>>,
  var_cache: VecMap<CompactString>,
}

impl AssignedVars {
  fn get_var(&mut self, var: Variable) -> &str {
    if self.var_cache.contains_key(var.id) {
      return &self.var_cache[var.id];
    }
    let mut res = CompactString::default();
    for term in self.assignments.remove(var.id).unwrap_or_default() {
      match term {
        Term::Terminal(Terminal(c)) => res.push(c),
        Term::Variable(var) => res += self.get_var(var),
      }
    }
    self.var_cache.insert(var.id, res);
    &self.var_cache[var.id]
  }
}
