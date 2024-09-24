#[allow(dead_code)]
mod vec_list;
use bit_set::BitSet;
use vec_list::VecList;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Terminal(pub char);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Variable {
    pub id: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
    /// listeners[x] = is a set of VecLlist-pointers for the clauses where variable with id x exists.
    pub listeners: Vec<BitSet>,
    pub ansestor_states: Vec<Solver>,
}

impl Solver {
    pub fn new(formula: Cnf, no_vars: usize) -> Self {
        let mut listeners = (0..no_vars)
            .map(|_| BitSet::with_capacity(no_vars))
            .collect::<Vec<_>>();
        for (clause_ptr, clause) in formula.0.iter() {
            for (_, term) in clause
                .equation
                .lhs
                .0
                .iter()
                .chain(clause.equation.rhs.0.iter())
            {
                if let Term::Variable(var) = term {
                    listeners[var.id].insert(clause_ptr.to_usize());
                }
            }
        }
        Self {
            formula,
            assignments: Vec::new(),
            listeners,
            ansestor_states: Vec::new(),
        }
    }

    #[expect(dead_code, unused_variables)]
    fn propagate(&mut self, clause_idx: usize) {
        todo!()
    }

    #[expect(dead_code, unused_variables)]
    fn fix_var(&mut self, var: Variable, val: Word) {
        todo!()
    }
}
