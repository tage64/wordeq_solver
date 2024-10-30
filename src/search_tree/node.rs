use std::collections::BTreeMap;
use std::ops::ControlFlow::{self, *};

use bit_set::BitSet;
use vec_map::VecMap;

use super::{SplitKind, Splits};
use crate::vec_list::{Entry, ListPtr};
use crate::*;

/// A result returned from the simplify_clause function.
#[derive(Debug, Clone)]
#[must_use]
enum SimplificationResult {
  /// Both LHS and RHS are empty.
  BothSidesEmpty,
  /// Unit propagation.
  UnitProp(UnitProp),
  /// Split on a variable at the start of LHS or RHS.
  Split(SplitKind),
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

/// A node in the search tree.
#[derive(Debug, Clone)]
pub struct SearchNode<'a> {
  /// The original formula.
  original_formula: &'a Formula,
  /// The formula to solve. Clauses may be removed or modified but new clauses will never be added.
  pub(super) formula: Cnf,
  /// assignments[x] = the value for variable with id x in the original formula.
  ///
  /// Note that the variable ids in the keys of this map corresponds to the variables in the
  /// original formula, while the variable ids in the values of this map as well as the variable
  /// ids in other parts of the solver changes over time. More specifically, if for instance the
  /// variable X gets assigned the value YX' where X' is a fresh variable, X' will reuse the id for
  /// X in all parts of the solver except the keys in this map.
  pub(super) assignments: VecMap<Word>,
  /// assignments_var_ptrs[x][y] = a bitset for occurences of the variable x in the original
  /// variable y.
  assignments_var_ptrs: VecMap<VecMap<BitSet>>,
  /// var_ptrs is a map with variable ids as keys, the values are maps of all clauses where that
  /// variable exists, they have clause pointers as keys and pairs (lhs_ptrs, rhs_ptrs) as
  /// values, where lhs_ptrs and rhs_ptrs are bitsets of pointers to
  /// variables in the LHS and RHS of that clause equation respectively.
  pub(super) var_ptrs: VecMap<VecMap<(BitSet, BitSet)>>,
  /// A set of pointers to all clauses which might have changed and should be checked.
  updated_clauses: BitSet,
  /// Splits is an ordered map with Splits as keys and clause indices as values.
  splits: BTreeMap<SplitKind, ListPtr>,
  /// splits[c] = the splits for clause c.
  splits_for_clause: VecMap<SplitKind>,
  /// The number of nodes above this node in the search tree.
  pub(super) depth: usize,
  /// The number of non reducing edges above this node in the search tree.
  pub(super) non_reducing_depth: usize,
}

impl<'a> SearchNode<'a> {
  pub(super) fn new(formula: Cnf, original_formula: &'a Formula) -> Self {
    let mut var_ptrs = VecMap::with_capacity(original_formula.no_vars());
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
      original_formula,
      formula,
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

  /// Run the fix point function and return SAT, UNSAT or a set of splits.
  pub(super) fn compute(
    mut self,
    node_watcher: &impl NodeWatcher,
  ) -> ControlFlow<Solution, (Self, Splits)> {
    if node_watcher.visit_node(&self).is_break() {
      return Break(Cancelled);
    }
    #[cfg(feature = "trace_logging")]
    log::trace!(
      "{:depth$}Solving formula: {}",
      "",
      self
        .formula
        .display(|x| &self.original_formula.var_names[x.id]),
      depth = self.depth,
    );
    self.assert_invariants();
    // Run the fix point function.
    let fix_point_res = self.fix_point();
    #[cfg(feature = "trace_logging")]
    log::trace!(
      "{:depth$}After fix_point(): {}",
      "",
      self
        .formula
        .display(|x| &self.original_formula.var_names[x.id]),
      depth = self.depth,
    );
    if let Err(()) = fix_point_res {
      // This node is unsat.
      #[cfg(feature = "trace_logging")]
      log::trace!("{:1$}Unsatisfiable branch;", "", self.depth);
      return Break(Unsat);
    }
    // Perform a split.
    let Some((split_kind, clause_ptr)) = self.splits.pop_first() else {
      // There are no splits so we've reached SAT!
      #[cfg(feature = "trace_logging")]
      log::trace!("SAT");
      return Break(Sat(SatResult::new((*self.original_formula).clone(), self)));
      // TODO: set should_exit.
    };
    self.splits_for_clause.remove(clause_ptr.to_usize());
    let splits = split_kind.create_splits(&self, clause_ptr);
    #[cfg(feature = "trace_logging")]
    log::trace!("{:depth$}New split;", "", depth = self.depth);
    Continue((self, splits))
  }

  #[cfg(debug_assertions)]
  fn assert_invariants(&self) {
    // Assert invariants related to self.var_ptrs and self.assignments.
    // Check that self.var_ptrs is sound.
    for var in (0..self.original_formula.no_vars()).map(|id| Variable { id }) {
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
      if let Some(splits) = self.splits_for_clause.get(clause_ptr.to_usize()) {
        assert_eq!(self.splits[splits], clause_ptr);
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
    for (splits, clause_ptr) in self.splits.iter() {
      assert_eq!(&self.splits_for_clause[clause_ptr.to_usize()], splits);
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
          SimplificationResult::Split(split) => {
            if let Some(prev_clause) = self.splits.insert(split.clone(), clause_ptr) {
              self.splits_for_clause.remove(prev_clause.to_usize());
            }
            self.splits_for_clause.insert(clause_ptr.to_usize(), split);
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
              self.fix_var(var, rhs.clone().0.iter().map(|(_, x)| x.clone()));
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
              self.fix_var(var, lhs.clone().0.iter().map(|(_, x)| x.clone()));
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
      let lhs_back = lhs_back_ptr.map(|x| lhs.0.get_mut(x));
      let rhs_back = rhs_back_ptr.map(|x| rhs.0.get_mut(x));
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
        (Some(Term::Variable(x)), Some(Term::Variable(y))) if x == y => {
          // Both sides ends with the same variable.
          // Check if we should remove from self.var_ptrs.
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
          lhs.0.remove(lhs_back_ptr.unwrap());
          rhs.0.remove(rhs_back_ptr.unwrap());
        }
        (Some(Term::Terminal(a)), Some(Term::Terminal(b))) => {
          if a == b {
            lhs.0.remove(lhs_back_ptr.unwrap());
            rhs.0.remove(rhs_back_ptr.unwrap());
          } else if a.0.ends_with(b.0.as_str()) {
            a.0.truncate(a.0.len() - b.0.len());
            rhs.0.remove(rhs_back_ptr.unwrap());
          } else if b.0.ends_with(a.0.as_str()) {
            b.0.truncate(b.0.len() - a.0.len());
            lhs.0.remove(lhs_back_ptr.unwrap());
          } else {
            // Rule 6: Both sides end with distinct terminals:
            return Err(());
          }
        }
        (Some(Term::Variable(_)), Some(_)) | (Some(_), Some(Term::Variable(_))) => break,
      }
    }
    // Remove equal terminals from the start and perform split.
    loop {
      let lhs_head_ptr = lhs.0.head();
      let rhs_head_ptr = rhs.0.head();
      let lhs_head = lhs_head_ptr.map(|x| lhs.0.get(x));
      let rhs_head = rhs_head_ptr.map(|x| rhs.0.get(x));
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
        (Some(Term::Variable(x)), Some(Term::Variable(y))) if x == y => {
          // Both sides starts with the same variable.
          // Check if we should remove from self.var_ptrs.
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
          lhs.0.remove(lhs_head_ptr.unwrap());
          rhs.0.remove(rhs_head_ptr.unwrap());
        }
        (Some(Term::Terminal(a)), Some(Term::Terminal(b))) => {
          if a == b {
            lhs.0.remove(lhs_head_ptr.unwrap());
            rhs.0.remove(rhs_head_ptr.unwrap());
          } else if a.0.starts_with(b.0.as_str()) {
            let Term::Terminal(a) = lhs.0.get_mut(lhs_head_ptr.unwrap()) else {
              unreachable!()
            };
            drop(a.0.drain(..b.0.len()));
            rhs.0.remove(rhs_head_ptr.unwrap());
          } else if b.0.starts_with(a.0.as_str()) {
            let Term::Terminal(b) = rhs.0.get_mut(rhs_head_ptr.unwrap()) else {
              unreachable!()
            };
            drop(b.0.drain(..a.0.len()));
            lhs.0.remove(lhs_head_ptr.unwrap());
          } else {
            // Rule 6: Both sides start with distinct terminals:
            return Err(());
          }
        }
        // Rule 7: One side starts with a terminal and the other starts with a variable.
        (Some(Term::Terminal(a)), Some(Term::Variable(x))) => {
          if rhs_head_ptr == rhs.0.back() {
            // RHS is a single variable.
            return Ok(UnitProp(UnitPropRhs(*x)));
          } else {
            return Ok(Split(SplitKind::EmptyOrTerminal(*x, a.clone(), Side::Rhs)));
          }
        }
        (Some(Term::Variable(x)), Some(Term::Terminal(a))) => {
          if lhs_head_ptr == lhs.0.back() {
            // LHS is a single variable.
            return Ok(UnitProp(UnitPropLhs(*x)));
          } else {
            return Ok(Split(SplitKind::EmptyOrTerminal(*x, a.clone(), Side::Lhs)));
          }
        }
        // Rule 8: Both sides starts with variables.
        (Some(Term::Variable(x)), Some(Term::Variable(y))) => {
          if lhs_head_ptr == lhs.0.back() {
            // LHS is a single variable.
            return Ok(UnitProp(UnitPropLhs(*x)));
          } else if rhs_head_ptr == rhs.0.back() {
            // RHS is a single variable.
            return Ok(UnitProp(UnitPropRhs(*y)));
          } else {
            return Ok(Split(SplitKind::TwoVars(*x, *y)));
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
    if let Some(splits) = self.splits_for_clause.remove(clause_ptr.to_usize()) {
      self.splits.remove(&splits);
    }
  }

  /// Given a variable and a value, replace all occurences of that variable with the value.
  pub(super) fn fix_var(&mut self, var: Variable, val: impl IntoIterator<Item = Term> + Clone) {
    #[cfg(feature = "trace_logging")]
    log::trace!(
      "{:depth$}fixing: {} = {}",
      "",
      &self.original_formula.var_names[var.id],
      display_word(val.clone().into_iter().collect::<Vec<_>>().iter(), |x| {
        &self.original_formula.var_names[x.id]
      }),
      depth = self.depth,
    );
    for (clause_id, (lhs_ptrs, rhs_ptrs)) in self.var_ptrs.remove(var.id).unwrap().iter() {
      self.updated_clauses.insert(clause_id);
      if let Some(splits) = self.splits_for_clause.remove(clause_id) {
        self.splits.remove(&splits);
      }
      let clause_ptr = ListPtr::from_usize(clause_id);
      let Clause {
        equation: Equation { lhs, rhs },
      } = self.formula.0.get_mut(clause_ptr);
      for term_ptr in lhs_ptrs.iter().map(ListPtr::from_usize) {
        for insert_term in val.clone() {
          if let Term::Variable(var) = &insert_term {
            let var = *var;
            let insert_ptr = lhs.0.insert_before(term_ptr, insert_term);
            self
              .var_ptrs
              .entry(var.id)
              .or_insert_with(VecMap::new)
              .entry(clause_id)
              .or_insert((BitSet::new(), BitSet::new()))
              .0
              .insert(insert_ptr.to_usize());
          } else {
            lhs.0.insert_before(term_ptr, insert_term);
          }
        }
        lhs.0.remove(term_ptr);
      }
      for term_ptr in rhs_ptrs.iter().map(ListPtr::from_usize) {
        for insert_term in val.clone() {
          if let Term::Variable(var) = &insert_term {
            let var = *var;
            let insert_ptr = rhs.0.insert_before(term_ptr, insert_term);
            self
              .var_ptrs
              .entry(var.id)
              .or_insert_with(VecMap::new)
              .entry(clause_id)
              .or_insert((BitSet::new(), BitSet::new()))
              .1
              .insert(insert_ptr.to_usize());
          } else {
            rhs.0.insert_before(term_ptr, insert_term);
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
            if let Term::Variable(x) = &insert_term {
              let x = *x;
              let insert_ptr = assignment.0.insert_before(term_ptr, insert_term);
              self
                .assignments_var_ptrs
                .entry(x.id)
                .or_insert_with(VecMap::new)
                .entry(orig_var_id)
                .or_insert_with(BitSet::new)
                .insert(insert_ptr.to_usize());
            } else {
              assignment.0.insert_before(term_ptr, insert_term);
            }
          }
          assignment.0.remove(term_ptr);
        }
      }
    }
    if let vec_map::Entry::Vacant(entry) = self.assignments.entry(var.id) {
      let mut assignment = Word::default();
      for insert_term in val.clone() {
        if let Term::Variable(x) = &insert_term {
          let x = *x;
          let insert_ptr = assignment.0.insert_back(insert_term);
          self
            .assignments_var_ptrs
            .entry(x.id)
            .or_insert_with(VecMap::new)
            .entry(var.id)
            .or_insert_with(BitSet::new)
            .insert(insert_ptr.to_usize());
        } else {
          assignment.0.insert_back(insert_term);
        }
      }
      entry.insert(assignment);
    }
  }

  /// Get an approximated list of the fields in this struct together with their dynamic sizes.
  pub fn get_sizes(&self) -> [(&'static str, usize); 8] {
    [
      (
        "formula",
        size_of::<SearchNode<'_>>()
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
        size_of::<BTreeMap<SplitKind, ListPtr>>()
          + self.splits.len() * (size_of::<SplitKind>() + size_of::<ListPtr>()),
      ),
      (
        "splits_for_clause",
        size_of::<VecMap<SplitKind>>() + self.splits_for_clause.capacity() * size_of::<SplitKind>(),
      ),
      ("last_static_items", size_of::<usize>() + size_of::<usize>()),
    ]
  }
}
