mod vec_list;
use arrayvec::ArrayVec;
use bit_set::BitSet;
use vec_list::{ListPtr, VecList};
use vec_map::VecMap;

/// Marker type for unsat.
#[derive(Debug, Clone, Copy)]
pub struct Unsat;

#[derive(Debug, Clone)]
#[must_use]
enum SimplificationResult {
  // The clause is a model.
  True,
  /// Unit propagation.
  UnitProp(UnitProp),
  /// Split on a variable. There will be at most three branches on one variable and the variable
  /// will be replaced with 0-2 term or fresh variables.
  Split(Branches),
}

/// Split on a variable. There will be at most three branches on one variable and the variable
/// will be replaced with 0-2 term or fresh variables.
#[derive(Debug, Clone)]
struct Branches(ArrayVec<(Variable, ArrayVec<TermOrFreshVar, 2>), 3>);

#[derive(Debug, Clone, Copy)]
#[must_use]
enum UnitProp {
  /// LHS consists of one single variable.
  UnitPropLhs(Variable),
  /// RHS consists of one single variable.
  UnitPropRhs(Variable),
}
use UnitProp::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Terminal(pub char);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Variable {
  pub id: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Term {
  Terminal(Terminal),
  Variable(Variable),
}

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
pub struct Word(pub VecList<Term>);

/// An equality constraint.
#[derive(Debug, Clone)]
pub struct Equation {
  pub lhs: Word,
  pub rhs: Word,
}

#[derive(Debug, Clone)]
pub struct Clause {
  /// This should be disjunction and negations but it is only an equation for now.
  pub equation: Equation,
}

#[derive(Debug, Clone)]
pub struct Cnf(pub VecList<Clause>);

#[derive(Debug, Clone)]
pub struct Solver {
  pub formula: Cnf,
  /// The number of variables. Maybe sparse, that is, some of the previously used variables might
  /// have been fixed but they still count.
  no_vars: usize,
  /// assignments[x] = the value for variable with id x.
  pub assignments: Vec<Option<Terminal>>,
  /// var_ptrs is a map with variable ids as keys, the values are maps of all clauses where that
  /// variable exists, they have clause pointers as keys and pairs (lhs_ptrs, rhs_ptrs) as
  /// values, where lhs_ptrs and rhs_ptrs are bitsets of pointers to
  /// variables in the LHS and RHS of that clause equation respectively.
  var_ptrs: VecMap<VecMap<(BitSet, BitSet)>>,
  /// A set of pointers to all clauses which might have changed and should be checked.
  updated_clauses: BitSet,
  /// splits[c] = a possible split at clause c.
  splits: VecMap<Branches>,
  parent: Option<Box<(Self, Branches)>>,
}

impl Solver {
  pub fn new(formula: Cnf, no_vars: usize) -> Self {
    let mut var_ptrs = VecMap::with_capacity(no_vars);
    for (clause_ptr, clause) in formula.0.iter() {
      for (term_ptr, term) in clause.equation.lhs.0.iter() {
        if let Term::Variable(var) = term {
          var_ptrs
            .entry(var.id)
            .or_insert(VecMap::new())
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
            .or_insert(VecMap::new())
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
      assignments: Vec::new(),
      var_ptrs,
      updated_clauses,
      splits: VecMap::new(),
      parent: None,
    }
  }

  pub fn solve(&mut self) -> Result<(), Unsat> {
    loop {
      if let Err(Unsat) = self.fix_point() {
        self.take_next_branch()?;
      }
      loop {
        let Some((clause_id, branches)) = self.splits.drain().next() else {
          return Ok(());
        };
        let clause_ptr = ListPtr::from_usize(clause_id);
        // Check that the clause still exists.
        if self.formula.0.contains_ptr(clause_ptr) {
          // Check that no of the variables have been fixed.
          if branches
            .0
            .iter()
            .all(|(var, _)| self.var_ptrs.contains_key(var.id))
          {
            let grand_parent = self.parent.take();
            let mut parent = self.clone();
            parent.parent = grand_parent;
            self.parent = Some(Box::new((parent, branches)));
            self.take_next_branch()?;
            break;
          }
        }
      }
    }
  }

  /// Take the next branch at the parent, grand parent or older ancestor. Returns Unsat if no more
  /// branches exist.
  fn take_next_branch(&mut self) -> Result<(), Unsat> {
    loop {
      let Some(mut parent) = self.parent.take() else {
        return Err(Unsat);
      };
      if let Some(branch) = parent.1 .0.pop() {
        // Restor self to parent.
        let grand_parent = parent.0.parent.take();
        *self = parent.0.clone();
        parent.0.parent = grand_parent;
        self.parent = Some(parent);
        // Make the split.
        let mut val: ArrayVec<Term, 2> = ArrayVec::new();
        for x in branch.1.iter() {
          match x {
            TermOrFreshVar::Term(t) => val.push(*t),
            FreshVar => val.push(Term::Variable(self.add_fresh_var())),
          }
        }
        self.fix_var(branch.0, val);
        break Ok(());
      }
      self.parent = parent.0.parent.take();
    }
  }

  fn fix_point(&mut self) -> Result<(), Unsat> {
    while !self.updated_clauses.is_empty() {
      let mut unit_propagations = Vec::new();
      while let Some(clause_ptr) = self.updated_clauses.iter().next().map(ListPtr::from_usize) {
        match self.simplify_equation(clause_ptr)? {
          SimplificationResult::True => self.remove_clause(clause_ptr),
          SimplificationResult::UnitProp(x) => unit_propagations.push((clause_ptr, x)),
          SimplificationResult::Split(s) => {
            self.splits.insert(clause_ptr.to_usize(), s);
          }
        }
      }

      // Perform unit propagations.
      for (clause_ptr, unit_prop) in unit_propagations.into_iter() {
        let Clause {
          equation: Equation { lhs, rhs },
        } = self.formula.0.get(clause_ptr);
        match unit_prop {
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
              self.remove_clause(clause_ptr);
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
              self.remove_clause(clause_ptr);
              if var_occurences != 1 {
                to_be_empty.insert(var.id);
              }
              for x in to_be_empty.iter() {
                self.fix_var(Variable { id: x }, []);
              }
            }
          }
        }
      }
    }
    Ok(())
  }

  fn simplify_equation(&mut self, clause_ptr: ListPtr) -> Result<SimplificationResult, Unsat> {
    use SimplificationResult::*;
    let Clause {
      equation: Equation { lhs, rhs },
    } = self.formula.0.get_mut(clause_ptr);
    Ok('outer: loop {
      match (lhs.0.head(), rhs.0.head()) {
        (None, None) => break True,           // Rule 2: LHS and RHS are empty.
        (None, Some(_)) => return Err(Unsat), // Rule 4: Only LHS is empty.
        (Some(_), None) => return Err(Unsat), // Rule 4: Only RHS is empty.
        (Some(lhs_head_ptr), Some(rhs_head_ptr)) => {
          let lhs_head = lhs.0.get(lhs_head_ptr);
          let rhs_head = rhs.0.get(rhs_head_ptr);
          let branches = match (*lhs_head, *rhs_head) {
            (x, y) if x == y => {
              // Both sides starts with the same terminal or variable.
              lhs.0.remove(lhs_head_ptr);
              rhs.0.remove(rhs_head_ptr);
              // Check if we should remove from self.var_ptrs.
              if let Term::Variable(x) = x {
                // We removed the variable x at both LHS and RHS.
                let vec_map::Entry::Occupied(mut entry) =
                  self.var_ptrs[x.id].entry(clause_ptr.to_usize())
                else {
                  unreachable!()
                };
                entry.get_mut().0.remove(lhs_head_ptr.to_usize());
                entry.get_mut().1.remove(rhs_head_ptr.to_usize());
                if entry.get().0.is_empty() && entry.get().1.is_empty() {
                  entry.remove();
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
          loop {
            match (lhs.0.back(), rhs.0.back()) {
              (None, None) => break 'outer True, // Rule 2: LHS and RHS are empty.
              (None, Some(_)) => return Err(Unsat), // Rule 4: Only LHS is empty.
              (Some(_), None) => return Err(Unsat), // Rule 4: Only RHS is empty.
              (Some(lhs_back_ptr), Some(rhs_back_ptr)) => {
                let lhs_back = lhs.0.get(lhs_back_ptr);
                let rhs_back = rhs.0.get(rhs_back_ptr);
                match (*lhs_back, *rhs_back) {
                  (x, y) if x == y => {
                    // Both sides ends with the same terminal or variable.
                    lhs.0.remove(lhs_back_ptr);
                    rhs.0.remove(rhs_back_ptr);
                    // Check if we should remove from self.var_ptrs.
                    if let Term::Variable(x) = x {
                      // We removed the variable x at both LHS and RHS.
                      let vec_map::Entry::Occupied(mut entry) =
                        self.var_ptrs[x.id].entry(clause_ptr.to_usize())
                      else {
                        unreachable!()
                      };
                      entry.get_mut().0.remove(lhs_back_ptr.to_usize());
                      entry.get_mut().1.remove(rhs_back_ptr.to_usize());
                      if entry.get().0.is_empty() && entry.get().1.is_empty() {
                        entry.remove();
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
                      break 'outer UnitProp(UnitPropRhs(x));
                    } else {
                      break;
                    }
                  }
                  (Term::Variable(x), Term::Terminal(_)) => {
                    if lhs_head_ptr == lhs_back_ptr {
                      // LHS is a single variable.
                      break 'outer UnitProp(UnitPropLhs(x));
                    } else {
                      break;
                    }
                  }
                  (Term::Variable(x), Term::Variable(y)) => {
                    if lhs_head_ptr == lhs_back_ptr {
                      // LHS is a single variable.
                      break 'outer UnitProp(UnitPropLhs(x));
                    } else if rhs_head_ptr == rhs_back_ptr {
                      // RHS is a single variable.
                      break 'outer UnitProp(UnitPropRhs(y));
                    } else {
                      break;
                    }
                  }
                }
              }
            }
          }
          break Split(branches);
        }
      }
    })
  }

  fn remove_clause(&mut self, clause_ptr: ListPtr) {
    // We will not get any ABA problems because we should only remove not add clauses.
    let Clause {
      equation: Equation { lhs, rhs },
    } = self.formula.0.remove(clause_ptr);
    // Remove all variable pointers from self.var_ptrs.
    for (_, term) in lhs.0.iter() {
      if let Term::Variable(var) = term {
        self.var_ptrs[var.id].remove(clause_ptr.to_usize());
      }
    }
    for (_, term) in rhs.0.iter() {
      if let Term::Variable(var) = term {
        self.var_ptrs[var.id].remove(clause_ptr.to_usize());
      }
    }
    self.updated_clauses.remove(clause_ptr.to_usize());
  }

  /// Given a variable and a value, replace all occurences of that variable with the value.
  fn fix_var(&mut self, var: Variable, val: impl IntoIterator<Item = Term> + Clone) {
    for (clause_id, (lhs_ptrs, rhs_ptrs)) in self.var_ptrs[var.id].iter() {
      self.updated_clauses.insert(clause_id);
      let clause_ptr = ListPtr::from_usize(clause_id);
      let Clause {
        equation: Equation { lhs, rhs },
      } = self.formula.0.get_mut(clause_ptr);
      for term_ptr in lhs_ptrs.iter().map(ListPtr::from_usize) {
        for insert_term in val.clone() {
          lhs.0.insert_before(term_ptr, insert_term);
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
  }

  /// Add a fresh variable and increment self.no_vars.
  fn add_fresh_var(&mut self) -> Variable {
    let new_var = Variable { id: self.no_vars };
    self.no_vars += 1;
    new_var
  }
}
