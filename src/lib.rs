mod vec_list;
use arrayvec::ArrayVec;
use bit_set::BitSet;
use vec_list::{ListPtr, VecList};
use vec_map::VecMap;

/// A terminal (a character).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Terminal(pub char);

/// A variable with a unique id.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

/// Marker type for unsat.
#[derive(Debug, Clone, Copy)]
pub struct Unsat;

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
}
use UnitProp::*;

/// Split on a variable. There will be at most three branches on one variable and the variable
/// will be replaced with 0-2 term or fresh variables.
#[derive(Debug, Clone)]
struct Branches(ArrayVec<(Variable, ArrayVec<TermOrFreshVar, 2>), 3>);

/// A Term or a fresh variable.
#[derive(Debug, Clone, Copy)]
enum TermOrFreshVar {
  Term(Term),
  /// Create a new fresh variable.
  FreshVar,
}
use TermOrFreshVar::FreshVar;

impl From<Variable> for TermOrFreshVar {
  fn from(x: Variable) -> Self {
    TermOrFreshVar::Term(Term::Variable(x))
  }
}

impl From<Terminal> for TermOrFreshVar {
  fn from(a: Terminal) -> Self {
    TermOrFreshVar::Term(Term::Terminal(a))
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
  /// var_ptrs is a map with variable ids as keys, the values are maps of all clauses where that
  /// variable exists, they have clause pointers as keys and pairs (lhs_ptrs, rhs_ptrs) as
  /// values, where lhs_ptrs and rhs_ptrs are bitsets of pointers to
  /// variables in the LHS and RHS of that clause equation respectively.
  var_ptrs: VecMap<VecMap<(BitSet, BitSet)>>,
  /// A set of pointers to all clauses which might have changed and should be checked.
  updated_clauses: BitSet,
  /// splits[c] = a possible split at clause c.
  ///
  /// splits and updated_clauses should be disjunct, the remaining clauses are true.
  splits: VecMap<Branches>,
  /// The parent of this node in the search tree together with the other branches to try under that
  /// parent.
  parent: Option<(Box<Self>, Branches)>,
}

impl Solver {
  pub fn new(formula: Cnf, no_vars: usize) -> Self {
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
      var_ptrs,
      updated_clauses,
      splits: VecMap::new(),
      parent: None,
    }
  }

  /// Assert invariants related to self.var_ptrs and self.assignments.
  #[allow(dead_code)]
  fn assert_vars_invariants(&self) {
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
  }

  /// Assert invariants about self.splits and self.updated_clauses.
  #[allow(dead_code)]
  fn assert_splits_and_updated_invariants(&self) {
    // Check that self.splits and self.updated_clauses point to valid clauses.
    self
      .splits
      .keys()
      .for_each(|x| assert!(self.formula.0.contains_ptr(ListPtr::from_usize(x))));
    self
      .updated_clauses
      .iter()
      .for_each(|x| assert!(self.formula.0.contains_ptr(ListPtr::from_usize(x))));
    // Check that self.splits and self.updated_clauses are valid.
    for (clause_ptr, clause) in self.formula.0.iter() {
      if self.updated_clauses.contains(clause_ptr.to_usize()) {
        assert!(!self.splits.contains_key(clause_ptr.to_usize()));
      }
      if let Some(branches) = self.splits.get(clause_ptr.to_usize()) {
        // Check that the branches points to valid splits.
        assert!(!self.updated_clauses.contains(clause_ptr.to_usize()));
        let Clause {
          equation: Equation { lhs, rhs },
        } = clause;
        for (var, _) in branches.0.iter() {
          assert!(self.var_ptrs.contains_key(var.id));
          let lhs_head = lhs.0.head().map(|x| *lhs.0.get(x));
          let rhs_head = rhs.0.head().map(|x| *rhs.0.get(x));
          let some_var = Some(Term::Variable(*var));
          assert!(
            lhs_head == some_var || rhs_head == some_var,
            "LHS head {:?} or RHS head {:?} should be the variable {:?}",
            lhs_head,
            rhs_head,
            var
          );
        }
      }
    }
  }

  fn assert_invariants(&self) {
    self.assert_vars_invariants();
    self.assert_splits_and_updated_invariants();
  }

  /// Solve the formula.
  pub fn solve(&mut self) -> Result<(), Unsat> {
    loop {
      self.assert_invariants();
      // Run the fix point function.
      if let Err(Unsat) = self.fix_point() {
        // This branch is unsat.
        self.take_next_branch()?;
        continue;
      }
      // Perform a split.
      let Some((_, branches)) = self.splits.drain().next() else {
        // There are no splits so we've reached SAT!
        return Ok(());
      };
      let grand_parent = self.parent.take();
      let mut parent = self.clone();
      parent.parent = grand_parent;
      self.parent = Some((Box::new(parent), branches));
      self.take_next_branch()?;
    }
  }

  /// Take the next branch at the parent, grand parent or older ancestor. Returns Unsat if no more
  /// branches exist.
  fn take_next_branch(&mut self) -> Result<(), Unsat> {
    loop {
      let Some((mut parent, mut branches)) = self.parent.take() else {
        return Err(Unsat);
      };
      if let Some((var, replacement)) = branches.0.pop() {
        // Restor self to parent.
        let grand_parent = parent.parent.take();
        *self = (*parent).clone();
        parent.parent = grand_parent;
        self.parent = Some((parent, branches));
        // Make the split.
        // Add all fresh variables.
        let mut replacement_fixed: ArrayVec<Term, 2> = ArrayVec::new();
        for x in replacement.iter() {
          match x {
            TermOrFreshVar::Term(t) => replacement_fixed.push(*t),
            FreshVar => replacement_fixed.push(Term::Variable(self.add_fresh_var())),
          }
        }
        self.fix_var(var, replacement_fixed);
        break Ok(());
      }
      // There are no more branches so let's backtrack to the grand parent.
      self.parent = parent.parent.take();
    }
  }

  /// In a loop: Simplify the equations and perform unit propagation.
  fn fix_point(&mut self) -> Result<(), Unsat> {
    while !self.updated_clauses.is_empty() {
      let mut unit_propagations = Vec::new();
      while let Some(clause_ptr) = self.updated_clauses.iter().next().map(ListPtr::from_usize) {
        match self.simplify_equation(clause_ptr)? {
          SimplificationResult::UnitProp(x) => unit_propagations.push((clause_ptr, x)),
          SimplificationResult::Split(s) => {
            self.splits.insert(clause_ptr.to_usize(), s);
          }
        }
      }

      // Perform unit propagations.
      for (clause_ptr, unit_prop) in unit_propagations.into_iter() {
        self.assert_invariants();
        let Clause {
          equation: Equation { lhs, rhs },
        } = self.formula.0.get(clause_ptr);
        match unit_prop {
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
  fn simplify_equation(&mut self, clause_ptr: ListPtr) -> Result<SimplificationResult, Unsat> {
    use SimplificationResult::*;
    let Clause {
      equation: Equation { lhs, rhs },
    } = self.formula.0.get_mut(clause_ptr);
    Ok(loop {
      let lhs_head_ptr = lhs.0.head();
      let rhs_head_ptr = rhs.0.head();
      let lhs_back_ptr = lhs.0.back();
      let rhs_back_ptr = rhs.0.back();
      let lhs_head = lhs_head_ptr.map(|x| *lhs.0.get(x));
      let rhs_head = rhs_head_ptr.map(|x| *rhs.0.get(x));
      let lhs_back = lhs_back_ptr.map(|x| *lhs.0.get(x));
      let rhs_back = rhs_back_ptr.map(|x| *rhs.0.get(x));
      match (lhs_head, rhs_head, lhs_back, rhs_back) {
        (None, Some(Term::Variable(_)) | None, _, Some(Term::Variable(_)) | None) => {
          // LHS is empty and RHS is empty or starts and ends with variables.
          break UnitProp(UnitPropEmptyLhs);
        }
        (Some(Term::Variable(_)), None, Some(Term::Variable(_)), _) => {
          // RHS is empty and LHS starts and ends with variables.
          break UnitProp(UnitPropEmptyRhs);
        }
        (None, Some(_), _, _) | (Some(_), None, _, _) => return Err(Unsat),
        (Some(lhs_head), Some(rhs_head), Some(lhs_back), Some(rhs_back)) => {
          match (lhs_back, rhs_back) {
            (x, y) if x == y => {
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
            (Term::Terminal(_), Term::Terminal(_)) => {
              return Err(Unsat);
            }
            (Term::Terminal(_), Term::Variable(x)) => {
              if rhs_head_ptr == rhs_back_ptr {
                // RHS is a single variable.
                break UnitProp(UnitPropRhs(x));
              }
            }
            (Term::Variable(x), Term::Terminal(_)) => {
              if lhs_head_ptr == lhs_back_ptr {
                // LHS is a single variable.
                break UnitProp(UnitPropLhs(x));
              }
            }
            (Term::Variable(x), Term::Variable(y)) => {
              if lhs_head_ptr == lhs_back_ptr {
                // LHS is a single variable.
                break UnitProp(UnitPropLhs(x));
              } else if rhs_head_ptr == rhs_back_ptr {
                // RHS is a single variable.
                break UnitProp(UnitPropRhs(y));
              }
            }
          }
          let branches = match (lhs_head, rhs_head) {
            (x, y) if x == y => {
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
              continue;
            }
            // Rule 6: Both sides start with distinct terminals:
            (Term::Terminal(_), Term::Terminal(_)) => {
              return Err(Unsat);
            }
            // Rule 7: One side starts with a terminal and the other starts with a variable.
            (Term::Terminal(a), Term::Variable(x)) | (Term::Variable(x), Term::Terminal(a)) => {
              Branches(
                [(x, ArrayVec::new()), (x, [a.into(), FreshVar].into())]
                  .into_iter()
                  .collect(),
              )
            }
            // Rule 8: Both sides starts with variables.
            (Term::Variable(x), Term::Variable(y)) => Branches(
              [
                (x, [y.into()].into_iter().collect()),
                (x, [y.into(), FreshVar].into()),
                (y, [x.into(), FreshVar].into()),
              ]
              .into(),
            ),
          };
          break Split(branches);
        }
        (None, _, Some(_), _)
        | (Some(_), _, None, _)
        | (_, None, _, Some(_))
        | (_, Some(_), _, None) => unreachable!(),
      }
    })
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
        self.var_ptrs[var.id].remove(clause_ptr.to_usize());
        if self.var_ptrs[var.id].is_empty() {
          self.var_ptrs.remove(var.id);
        }
      }
    }
    for (_, term) in rhs.0.iter() {
      if let Term::Variable(var) = term {
        self.var_ptrs[var.id].remove(clause_ptr.to_usize());
        if self.var_ptrs[var.id].is_empty() {
          self.var_ptrs.remove(var.id);
        }
      }
    }
    self.updated_clauses.remove(clause_ptr.to_usize());
    self.splits.remove(clause_ptr.to_usize());
  }

  /// Given a variable and a value, replace all occurences of that variable with the value.
  fn fix_var(&mut self, var: Variable, val: impl IntoIterator<Item = Term> + Clone) {
    // Debug assert:
    assert!(
      val
        .clone()
        .into_iter()
        .find(|x| *x == Term::Variable(var))
        .is_none()
    );
    for (clause_id, (lhs_ptrs, rhs_ptrs)) in self.var_ptrs[var.id].clone().iter() {
      self.updated_clauses.insert(clause_id);
      self.splits.remove(clause_id);
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
          rhs.0.insert_before(term_ptr, insert_term);
        }
        rhs.0.remove(term_ptr);
      }
    }
    self.var_ptrs.remove(var.id);
    self.assignments.insert(var.id, val.into_iter().collect());
  }

  /// Add a fresh variable and increment self.no_vars.
  fn add_fresh_var(&mut self) -> Variable {
    let new_var = Variable { id: self.no_vars };
    self.no_vars += 1;
    new_var
  }
}
