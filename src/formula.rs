use std::collections::HashMap;
use std::fmt;

use compact_str::CompactString;

use crate::vec_list::VecList;

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

/// A formula.
#[derive(Debug, Clone)]
pub struct Formula {
  pub(crate) cnf: Cnf,
  pub(crate) var_names: Vec<CompactString>,
}

impl Formula {
  pub fn new(cnf: Cnf, var_names: Vec<CompactString>) -> Self {
    Self { cnf, var_names }
  }

  pub fn from_strs(equations: &[(&str, &str)], mut is_variable: impl FnMut(char) -> bool) -> Self {
    let mut used_vars = HashMap::<char, usize>::new(); // Variables and there assigned numbers.
    let mut cnf = Cnf(VecList::with_capacity(equations.len()));
    for (text_lhs, text_rhs) in equations {
      let mut lhs = Word(VecList::with_capacity(text_lhs.len()));
      let mut rhs = Word(VecList::with_capacity(text_rhs.len()));
      for c in text_lhs.chars() {
        let term = if is_variable(c) {
          let next_var_id = used_vars.len();
          Term::Variable(Variable {
            id: *used_vars.entry(c).or_insert(next_var_id),
          })
        } else {
          Term::Terminal(Terminal(c))
        };
        lhs.0.insert_back(term);
      }
      for c in text_rhs.chars() {
        let term = if is_variable(c) {
          let next_var_id = used_vars.len();
          Term::Variable(Variable {
            id: *used_vars.entry(c).or_insert(next_var_id),
          })
        } else {
          Term::Terminal(Terminal(c))
        };
        rhs.0.insert_back(term);
      }
      cnf.0.insert_back(Clause {
        equation: Equation { lhs, rhs },
      });
    }
    let mut var_names = used_vars.keys().copied().collect::<Vec<char>>();
    var_names.sort_unstable_by_key(|x| used_vars[x]);
    let var_names = var_names
      .into_iter()
      .map(|c| c.to_string().into())
      .collect();
    Self::new(cnf, var_names)
  }
}

pub fn display_word<'a, D: fmt::Display>(
  word: impl IntoIterator<Item = &'a Term> + Clone,
  get_var_name: impl Fn(&Variable) -> D,
) -> impl fmt::Display {
  struct Displayer<F, W>(W, F);
  impl<'a, F, W, D> fmt::Display for Displayer<F, W>
  where
    W: IntoIterator<Item = &'a Term> + Clone,
    F: Fn(&Variable) -> D,
    D: fmt::Display,
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      for x in self.0.clone() {
        match x {
          Term::Terminal(Terminal(t)) => write!(f, "{t}")?,
          Term::Variable(v) => write!(f, "{}", (self.1)(&v))?,
        }
      }
      Ok(())
    }
  }
  Displayer(word, get_var_name)
}

impl Cnf {
  pub fn display<'a, D: fmt::Display>(
    &'a self,
    get_var_name: impl Fn(&Variable) -> D + 'a,
  ) -> impl fmt::Display + 'a {
    struct Displayer<'a, F>(&'a Cnf, F);
    impl<'a, F, D> fmt::Display for Displayer<'a, F>
    where
      F: Fn(&Variable) -> D,
      D: fmt::Display,
    {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (clause_ptr, clause) in self.0.0.iter() {
          write!(
            f,
            "{}",
            display_word(clause.equation.lhs.0.iter().map(|(_, x)| x), &self.1)
          )?;
          write!(f, " = ")?;
          write!(
            f,
            "{}",
            display_word(clause.equation.rhs.0.iter().map(|(_, x)| x), &self.1)
          )?;
          if clause_ptr != self.0.0.back().unwrap() {
            write!(f, "; ")?;
          }
        }
        Ok(())
      }
    }
    Displayer(self, get_var_name)
  }
}

impl fmt::Display for Formula {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.cnf.display(|x| &self.var_names[x.id]).fmt(f)
  }
}
