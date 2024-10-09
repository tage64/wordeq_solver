mod vec_list;
use std::collections::BTreeMap;
use std::fmt;

use arrayvec::ArrayVec;
use bit_set::BitSet;
use vec_list::{ListPtr, VecList};
use vec_map::VecMap;

const MAX_DEPTH: usize = 16;
const INITIAL_MAX_DEPTH: usize = 4;

/// A terminal (a character).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Terminal(pub char);

/// A variable with a unique id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Variable {
  pub id: usize,
}

/// A terminal or variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Term {
  Terminal(Terminal),
  Variable(Variable),
}

/// A word is a list of terms.
#[derive(Debug, Clone)]
pub struct Word(pub VecList<Term>);

/// An equality constraint.
#[derive(Debug, Clone)]
pub struct Equation {
  pub lhs: Word,
  pub rhs: Word,
}

/// A clause in a conjunction.
#[derive(Debug, Clone)]
pub struct Clause {
  /// This could be extended to be disjunction and negations but it is only an equation for now.
  pub equation: Equation,
}

/// A list of clauses.
#[derive(Debug, Clone)]
pub struct Cnf(pub VecList<Clause>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnsatOrUnknown {
  Unsat,
  Unknown,
}
pub use UnsatOrUnknown::*;

/// A result returned from the simplify_clause function.
#[derive(Debug, Clone)]
#[must_use]
enum SimplificationResult {
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
  /// Both LHS and RHS are empty.
  BothSidesEmpty,
}
use UnitProp::*;

/// Branches for a clause involving one or two variables and 0 or one terminals.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Branches {
  /// One variable equal to only the empty string.
  Empty(Variable),
  /// One variable equal to the empty string or a terminal followed by a fresh variable.
  EmptyOrTerminal(Variable, Terminal),
  /// Two variables which might be equal or one might be a prefix of the other.
  TwoVars(Variable, Variable),
}

impl Branches {
  /// The number of splits (1..=3).
  fn len(&self) -> usize {
    match self {
      Self::Empty(_) => 1,
      Self::EmptyOrTerminal(_, _) => 2,
      Self::TwoVars(_, _) => 3,
    }
  }

  /// Get the nth split as a tuple (var, replacement).
  fn get(
    &self,
    n: usize,
    get_fresh_var: impl FnOnce(Variable) -> Variable,
  ) -> (Variable, ArrayVec<Term, 2>) {
    match (self, n) {
      (Self::Empty(x), 0) | (Self::EmptyOrTerminal(x, _), 0) => (*x, ArrayVec::new()),
      (Self::EmptyOrTerminal(x, a), 1) => (
        *x,
        [Term::Terminal(*a), Term::Variable(get_fresh_var(*x))].into(),
      ),
      (Self::TwoVars(x, y), 0) => (*x, [Term::Variable(*y)].into_iter().collect()),
      (Self::TwoVars(x, y), 1) | (Self::TwoVars(y, x), 2) => (
        *x,
        [Term::Variable(*y), Term::Variable(get_fresh_var(*x))].into(),
      ),
      _ => unreachable!(),
    }
  }
}

#[derive(Debug, Clone)]
pub struct Solver {
  /// The formula to solve. Clauses may be removed or modified but new clauses will never be added.
  formula: Cnf,
  /// The number of variables. Maybe sparse, that is, some of the previously used variables might
  /// have been fixed but they still count.
  no_vars: usize,
  /// assignments[x] = the value for variable with id x.
  pub assignments: VecMap<Vec<Term>>,
  /// var_names[x] = the name for variable with id x.
  var_names: Vec<String>,
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
  /// The parent of this node in the search tree together with the other branches to try under that
  /// parent.
  parent: Option<ParentNode>,
  max_depth: usize,
}

#[derive(Debug, Clone)]
struct ParentNode {
  solver: Box<Solver>,
  /// The branches under this node.
  branches: Branches,
  /// The current branch index.
  branch_idx: usize,
  /// The number of parents above the current node. This field will never be 0.
  depth: usize,
}

impl Solver {
  pub fn new(formula: Cnf, no_vars: usize, var_names: Vec<String>) -> Self {
    assert_eq!(no_vars, var_names.len());
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
      var_names,
      assignments: VecMap::new(),
      var_ptrs,
      updated_clauses,
      splits: BTreeMap::new(),
      splits_for_clause: VecMap::new(),
      parent: None,
      max_depth: INITIAL_MAX_DEPTH,
    }
  }

  #[allow(dead_code)]
  fn display_word<'a>(
    &'a self,
    word: impl Iterator<Item = &'a Term> + Clone + 'a,
  ) -> impl fmt::Display + 'a {
    struct Displayer<'a, I>(I, &'a Solver);
    impl<'a, I> fmt::Display for Displayer<'a, I>
    where
      I: Iterator<Item = &'a Term> + Clone + 'a,
    {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for x in self.0.clone() {
          match x {
            Term::Terminal(Terminal(t)) => write!(f, "{t}")?,
            Term::Variable(v) => write!(f, "{}", &self.1.var_names[v.id])?,
          }
        }
        Ok(())
      }
    }
    Displayer(word, self)
  }

  #[allow(dead_code)]
  fn display_formula(&self) -> impl fmt::Display + '_ {
    struct Displayer<'a>(&'a Solver);
    impl<'a> fmt::Display for Displayer<'a> {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (clause_ptr, clause) in self.0.formula.0.iter() {
          write!(
            f,
            "{}",
            self
              .0
              .display_word(clause.equation.lhs.0.iter().map(|(_, x)| x))
          )?;
          write!(f, " = ")?;
          write!(
            f,
            "{}",
            self
              .0
              .display_word(clause.equation.rhs.0.iter().map(|(_, x)| x))
          )?;
          if clause_ptr != self.0.formula.0.back().unwrap() {
            write!(f, "; ")?;
          }
        }
        Ok(())
      }
    }
    Displayer(self)
  }

  #[cfg(debug_assertions)]
  fn assert_invariants(&self) {
    // Assert invariants related to self.var_ptrs and self.assignments.
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
    let mut depth = solver.depth();
    while let Some(parent_node) = solver.parent.as_ref() {
      solver = &*parent_node.solver;
      assert_eq!(depth, solver.depth() + 1);
      depth = solver.depth();
    }
    assert_eq!(depth, 0);
  }
  #[cfg(not(debug_assertions))]
  fn assert_invariants(&self) {}

  /// Solve the formula.
  pub fn solve(&mut self) -> Result<(), UnsatOrUnknown> {
    while self.max_depth <= MAX_DEPTH {
      let mut unknown_branches = 0;
      loop {
        log::trace!(
          "{:depth$}Solving formula: {}",
          "",
          self.display_formula(),
          depth = self.depth()
        );
        self.assert_invariants();
        // Run the fix point function.
        let fix_point_res = self.fix_point();
        log::trace!(
          "{:depth$}After fix_point(): {}",
          "",
          self.display_formula(),
          depth = self.depth()
        );
        if let Err(e) = fix_point_res {
          debug_assert_eq!(e, Unsat);
          // This branch is unsat.
          log::trace!("{:1$}Unsatisfiable branch;", "", self.depth());
          if let Err(()) = self.take_next_branch() {
            break;
          }
          continue;
        }
        let depth = self.depth() + 1;
        if depth >= self.max_depth {
          unknown_branches += 1;
          if let Err(()) = self.take_next_branch() {
            break;
          }
          continue;
        }
        // Perform a split.
        let Some((branches, clause_ptr)) = self.splits.pop_first() else {
          // There are no splits so we've reached SAT!
          log::trace!("SAT");
          return Ok(());
        };
        self.splits_for_clause.remove(clause_ptr.to_usize());
        log::trace!("{:1$}New split;", "", self.depth());
        let grand_parent = self.parent.take();
        let mut parent = self.clone();
        parent.parent = grand_parent;
        self.parent = Some(ParentNode {
          solver: Box::new(parent),
          branches,
          branch_idx: 0,
          depth,
        });
        if let Err(()) = self.take_next_branch() {
          break;
        }
      }
      if unknown_branches == 0 {
        return Err(Unsat);
      }
      self.max_depth *= 2;
      log::trace!("Increasing max depth to {}", self.max_depth);
    }
    return Err(Unknown);
  }

  /// Take the next branch at the parent, grand parent or older ancestor. Returns Err(()) if no more
  /// branches exist.
  fn take_next_branch(&mut self) -> Result<(), ()> {
    loop {
      let Some(mut parent) = self.parent.take() else {
        log::trace!("UNSAT");
        return Err(());
      };
      let depth = parent.depth - 1;
      if parent.branch_idx < parent.branches.len() {
        log::trace!(
          "{:depth$}There are {} branches here.",
          "",
          parent.branches.len() - parent.branch_idx,
        );
        // restor self to parent.
        let grand_parent = parent.solver.parent.take();
        *self = (*parent.solver).clone();
        parent.solver.parent = grand_parent;
        let (branch_var, replacement) = parent
          .branches
          .get(parent.branch_idx, |x| self.add_fresh_var(x));
        parent.branch_idx += 1;
        self.parent = Some(parent);
        // make the split.
        log::trace!(
          "{:depth$}branching: {} = {}",
          "",
          &self.var_names[branch_var.id],
          self.display_word(replacement.iter())
        );
        self.fix_var(branch_var, replacement);
        break Ok(());
      }
      // There are no more branches so let's backtrack to the grand parent.
      *self = *parent.solver;
      log::trace!("{:depth$}Back tracking to: {}", "", self.display_formula(),);
    }
  }

  /// In a loop: Simplify the equations and perform unit propagation.
  fn fix_point(&mut self) -> Result<(), UnsatOrUnknown> {
    while !self.updated_clauses.is_empty() {
      let mut unit_propagation = None;
      while let Some(clause_ptr) = self.updated_clauses.iter().next().map(ListPtr::from_usize) {
        self.updated_clauses.remove(clause_ptr.to_usize());
        match self.simplify_equation(clause_ptr)? {
          SimplificationResult::UnitProp(x) => {
            if unit_propagation.is_none() {
              unit_propagation = Some((clause_ptr, x));
            }
          }
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
      if let Some((clause_ptr, unit_prop)) = unit_propagation {
        self.assert_invariants();
        let Clause {
          equation: Equation { lhs, rhs },
        } = self.formula.0.get(clause_ptr);
        match unit_prop {
          BothSidesEmpty => (),
          UnitPropEmptyLhs => {
            let mut to_be_empty = BitSet::new(); // All variables in RHS.
            for (_, term) in rhs.0.iter() {
              match *term {
                Term::Terminal(_) => return Err(Unsat),
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
                Term::Terminal(_) => return Err(Unsat),
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
                  Term::Terminal(_) => return Err(Unsat),
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
                  Term::Terminal(_) => return Err(Unsat),
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

  /// Simplify an equation as much as possible.
  fn simplify_equation(
    &mut self,
    clause_ptr: ListPtr,
  ) -> Result<SimplificationResult, UnsatOrUnknown> {
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
        (None, None) => return Ok(UnitProp(BothSidesEmpty)),
        (None, Some(Term::Variable(_))) => {
          if let Term::Terminal(_) = rhs.0.get(rhs.0.head().unwrap()) {
            return Err(Unsat);
          } else {
            // LHS is empty and RHS is empty or starts and ends with variables.
            return Ok(UnitProp(UnitPropEmptyLhs));
          }
        }
        (Some(Term::Variable(_)), None) => {
          if let Term::Terminal(_) = lhs.0.get(lhs.0.head().unwrap()) {
            return Err(Unsat);
          } else {
            // RHS is empty and LHS starts and ends with variables.
            return Ok(UnitProp(UnitPropEmptyRhs));
          }
        }
        (None, Some(Term::Terminal(_))) | (Some(Term::Terminal(_)), None) => return Err(Unsat),
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
          return Err(Unsat);
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
        (None, None) => return Ok(UnitProp(BothSidesEmpty)),
        (None, Some(Term::Variable(_))) => {
          if let Term::Terminal(_) = rhs.0.get(rhs.0.head().unwrap()) {
            return Err(Unsat);
          } else {
            // LHS is empty and RHS is empty or starts and ends with variables.
            return Ok(UnitProp(UnitPropEmptyLhs));
          }
        }
        (Some(Term::Variable(_)), None) => {
          if let Term::Terminal(_) = lhs.0.get(lhs.0.head().unwrap()) {
            return Err(Unsat);
          } else {
            // RHS is empty and LHS starts and ends with variables.
            return Ok(UnitProp(UnitPropEmptyRhs));
          }
        }
        (None, Some(Term::Terminal(_))) | (Some(Term::Terminal(_)), None) => return Err(Unsat),
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
          return Err(Unsat);
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
    // TODO: Debug assert:
    assert!(
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
  fn add_fresh_var(&mut self, from: Variable) -> Variable {
    let new_var = Variable { id: self.no_vars };
    self.no_vars += 1;
    let name = self.var_names[from.id].clone() + "'";
    self.var_names.push(name);
    new_var
  }

  /// Get the current depth in the tree.
  fn depth(&self) -> usize {
    self.parent.as_ref().map_or(0, |x| x.depth)
  }
}

#[cfg(test)]
mod tests {
  use flexi_logger::Logger;
  use rand::prelude::*;

  use super::*;

  #[test]
  fn test_solver() {
    let formula_1 = Cnf(VecList::new());
    assert_eq!(Solver::new(formula_1, 0, vec![]).solve(), Ok(()));
    let formula_2 = Cnf(
      [Clause {
        equation: Equation {
          lhs: Word(VecList::new()),
          rhs: Word(VecList::new()),
        },
      }]
      .into_iter()
      .collect(),
    );
    assert_eq!(Solver::new(formula_2, 0, vec![]).solve(), Ok(()));
    let formula_3 = Cnf(
      [Clause {
        equation: Equation {
          lhs: Word([Term::Terminal(Terminal('a'))].into_iter().collect()),
          rhs: Word(VecList::new()),
        },
      }]
      .into_iter()
      .collect(),
    );
    assert_eq!(Solver::new(formula_3, 0, vec![]).solve(), Err(Unsat));
  }

  #[test]
  fn random_sat_tests() {
    let mut logger = Logger::try_with_env_or_str("warn")
      .unwrap()
      .format(|f, _, r| write!(f, "{}", r.args()))
      .log_to_stdout()
      .start()
      .unwrap();
    let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(42);
    let var_names: [&str; 8] = ["X", "Y", "Z", "U", "V", "W", "P", "Q"];
    let var_index = |var_name: char| {
      var_names
        .iter()
        .position(|x| x.chars().next().unwrap() == var_name)
        .unwrap()
    };
    // The 286th iteration takes a lot of time.
    for test_i in 0..285 {
      //if test_i == 285 {
      //  logger.parse_new_spec("trace").unwrap();
      //}
      log::info!("Test iteration: {test_i}");
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
      // Create the CNF.
      let cnf = Cnf(
        lhss
          .iter()
          .zip(rhss.iter())
          .map(|(lhs_str, rhs_str)| {
            let lhs = Word(
              lhs_str
                .chars()
                .map(|c| {
                  if c == 'a' || c == 'b' {
                    Term::Terminal(Terminal(c))
                  } else {
                    Term::Variable(Variable { id: var_index(c) })
                  }
                })
                .collect(),
            );
            let rhs = Word(
              rhs_str
                .chars()
                .map(|c| {
                  if c == 'a' || c == 'b' {
                    Term::Terminal(Terminal(c))
                  } else {
                    Term::Variable(Variable { id: var_index(c) })
                  }
                })
                .collect(),
            );
            Clause {
              equation: Equation { lhs, rhs },
            }
          })
          .collect(),
      );
      let mut solver = Solver::new(
        cnf,
        n_variables,
        var_names
          .iter()
          .take(n_variables)
          .map(|x| x.to_string())
          .collect(),
      );
      assert!(solver.solve().is_ok());
    }
  }
}
