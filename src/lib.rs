#[allow(dead_code)]
mod vec_list;
use bit_set::BitSet;
use vec_list::{ListPtr, VecList};
use vec_map::VecMap;

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
    /// assignments[x] = the value for variable with id x.
    pub assignments: Vec<Option<Terminal>>,
    /// var_ptrs is a map with variable ids as keys, the values are maps of all clauses where that
    /// variable exists, they have clause pointers as keys and pairs (lhs_ptrs, rhs_ptrs) as
    /// values, where lhs_ptrs and rhs_ptrs are bitsets of pointers to
    /// variables in the LHS and RHS of that clause equation respectively.
    var_ptrs: VecMap<VecMap<(BitSet, BitSet)>>,
    pub ansestor_states: Vec<Solver>,
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
        Self {
            formula,
            assignments: Vec::new(),
            var_ptrs,
            ansestor_states: Vec::new(),
        }
    }

    #[expect(unused_variables)]
    fn propagate_clause(&mut self, clause_ptr: ListPtr) {
        todo!()
    }

    /// Given a variable and a value, replace all occurences of that variable with the value.
    #[expect(dead_code)]
    fn fix_var(&mut self, var: Variable, val: Word) {
        let mut clauses = BitSet::new();
        for (clause_id, (lhs_ptrs, rhs_ptrs)) in self.var_ptrs[var.id].iter() {
            clauses.insert(clause_id);
            let clause_ptr = ListPtr::from_usize(clause_id);
            let Clause {
                equation: Equation { lhs, rhs },
            } = self.formula.0.get_mut(clause_ptr);
            for term_ptr in lhs_ptrs.iter().map(ListPtr::from_usize) {
                for (_, insert_term) in val.0.iter() {
                    lhs.0.insert_before(term_ptr, *insert_term);
                }
                lhs.0.remove(term_ptr);
            }
            for term_ptr in rhs_ptrs.iter().map(ListPtr::from_usize) {
                for (_, insert_term) in val.0.iter() {
                    rhs.0.insert_before(term_ptr, *insert_term);
                }
                rhs.0.remove(term_ptr);
            }
        }
        for clause_ptr in clauses.iter().map(ListPtr::from_usize) {
            self.propagate_clause(clause_ptr);
        }
    }
}
