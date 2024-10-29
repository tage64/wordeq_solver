mod eq_parser;
use std::collections::HashMap;
use std::fmt;
use std::mem;

use compact_str::CompactString;
use serde::{Deserialize, Serialize};

use crate::vec_list::VecList;

/// A terminal (a character).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Terminal(pub CompactString);

/// A variable with a unique id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Variable {
  pub id: usize,
}

/// A terminal or variable.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Term {
  Terminal(Terminal),
  Variable(Variable),
}

/// A word is a list of terms.
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct Word(pub VecList<Term>);

/// An equality constraint.
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct Equation {
  pub lhs: Word,
  pub rhs: Word,
}

/// A clause in a conjunction.
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct Clause {
  /// This could be extended to be disjunction and negations but it is only an equation for now.
  pub equation: Equation,
}

/// A list of clauses.
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct Cnf(pub VecList<Clause>);

/// A formula.
#[derive(Debug, Clone, Serialize, Deserialize)]
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
      let mut curr_lhs_terminal = CompactString::default();
      for c in text_lhs.chars() {
        if is_variable(c) {
          if !curr_lhs_terminal.is_empty() {
            lhs.0.insert_back(Term::Terminal(Terminal(mem::replace(
              &mut curr_lhs_terminal,
              Default::default(),
            ))));
          }
          let next_var_id = used_vars.len();
          lhs.0.insert_back(Term::Variable(Variable {
            id: *used_vars.entry(c).or_insert(next_var_id),
          }));
        } else {
          curr_lhs_terminal.push(c);
        }
      }
      if !curr_lhs_terminal.is_empty() {
        lhs
          .0
          .insert_back(Term::Terminal(Terminal(curr_lhs_terminal)));
      }
      let mut rhs = Word(VecList::with_capacity(text_rhs.len()));
      let mut curr_rhs_terminal = CompactString::default();
      for c in text_rhs.chars() {
        if is_variable(c) {
          if !curr_rhs_terminal.is_empty() {
            rhs.0.insert_back(Term::Terminal(Terminal(mem::replace(
              &mut curr_rhs_terminal,
              Default::default(),
            ))));
          }
          let next_var_id = used_vars.len();
          rhs.0.insert_back(Term::Variable(Variable {
            id: *used_vars.entry(c).or_insert(next_var_id),
          }));
        } else {
          curr_rhs_terminal.push(c);
        }
      }
      if !curr_rhs_terminal.is_empty() {
        rhs
          .0
          .insert_back(Term::Terminal(Terminal(curr_rhs_terminal)));
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

  /// Parse a .eq file.
  pub fn from_eq_file(text: &str) -> anyhow::Result<Self> {
    eq_parser::EqParser::parse_to_formula(text)
  }

  /// The number of variables in this formula.
  pub fn no_vars(&self) -> usize {
    self.var_names.len()
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
          Term::Variable(v) => write!(f, "{}", (self.1)(v))?,
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
    impl<F, D> fmt::Display for Displayer<'_, F>
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
