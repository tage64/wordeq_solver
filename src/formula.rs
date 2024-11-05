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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BorrowedTerm<'a> {
  Terminal(&'a str),
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

/// A side in an equation, LHS or RHS.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Side {
  Lhs,
  Rhs,
}
pub use Side::*;

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

impl Term {
  fn borrow(&self) -> BorrowedTerm<'_> {
    match self {
      Term::Variable(x) => BorrowedTerm::Variable(*x),
      Term::Terminal(Terminal(s)) => BorrowedTerm::Terminal(s.as_str()),
    }
  }
}

impl Word {
  pub fn from_str_split_terminals(
    text: &str,
    mut get_var: impl FnMut(char) -> Option<Variable>,
    mut split_terminal: impl FnMut(&str, char) -> bool,
  ) -> Word {
    let mut word = Word(VecList::new());
    let mut curr_word_terminal = CompactString::default();
    for c in text.chars() {
      let maybe_var = get_var(c);
      if !curr_word_terminal.is_empty()
        && (maybe_var.is_some() || split_terminal(&curr_word_terminal, c))
      {
        word.0.insert_back(Term::Terminal(Terminal(mem::replace(
          &mut curr_word_terminal,
          Default::default(),
        ))));
      }
      if let Some(var) = maybe_var {
        word.0.insert_back(Term::Variable(var));
      } else {
        curr_word_terminal.push(c);
      }
    }
    if !curr_word_terminal.is_empty() {
      word
        .0
        .insert_back(Term::Terminal(Terminal(curr_word_terminal)));
    }
    word
  }

  pub fn from_str(text: &str, get_var: impl FnMut(char) -> Option<Variable>) -> Word {
    Self::from_str_split_terminals(text, get_var, |_, _| false)
  }
}

impl PartialEq for Word {
  fn eq(&self, other: &Self) -> bool {
    let mut iter1 = self.0.iter().map(|(_, t)| t.borrow());
    let mut iter2 = other.0.iter().map(|(_, t)| t.borrow());
    let mut leading_terminal_1 = None;
    let mut leading_terminal_2 = None;
    loop {
      use BorrowedTerm::*;
      match (
        leading_terminal_1.take().or_else(|| iter1.next()),
        leading_terminal_2.take().or_else(|| iter2.next()),
      ) {
        (None, None) => return true,
        (Some(_), None)
        | (None, Some(_))
        | (Some(Variable(_)), Some(Terminal(_)))
        | (Some(Terminal(_)), Some(Variable(_))) => return false,
        (Some(Variable(x)), Some(Variable(y))) if x != y => return false,
        (Some(Terminal(t1)), Some(Terminal(t2))) if t1 != t2 => {
          if t1.starts_with(t2) {
            leading_terminal_1 = Some(Terminal(&t1[t2.len()..]));
          } else if t2.starts_with(t1) {
            leading_terminal_2 = Some(Terminal(&t2[t1.len()..]));
          } else {
            return false;
          }
        }
        _ => (),
      }
    }
  }
}

impl Eq for Word {}

impl Equation {
  /// Get a side of the equation.
  pub fn side(&self, side: Side) -> &Word {
    let Self { lhs, rhs } = self;
    match side {
      Lhs => lhs,
      Rhs => rhs,
    }
  }
}

impl Side {
  /// Get the other side.
  pub fn opposite(self) -> Self {
    match self {
      Lhs => Rhs,
      Rhs => Lhs,
    }
  }
}

impl Formula {
  pub fn new(cnf: Cnf, var_names: Vec<CompactString>) -> Self {
    Self { cnf, var_names }
  }

  pub fn from_strs(equations: &[(&str, &str)], mut is_variable: impl FnMut(char) -> bool) -> Self {
    let mut used_vars = HashMap::<char, usize>::new(); // Variables and there assigned numbers.
    let mut get_var = |c: char| {
      if is_variable(c) {
        let next_var_id = used_vars.len();
        Some(Variable {
          id: *used_vars.entry(c).or_insert(next_var_id),
        })
      } else {
        None
      }
    };
    let mut cnf = Cnf(VecList::with_capacity(equations.len()));
    for (text_lhs, text_rhs) in equations {
      let lhs = Word::from_str(text_lhs, &mut get_var);
      let rhs = Word::from_str(text_rhs, &mut get_var);
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

#[cfg(test)]
mod tests {
  use std::cell::RefCell;

  use rand::distributions::{Alphanumeric, DistString};
  use rand::prelude::*;

  use super::*;

  #[test]
  fn test_word_eq() {
    let rng = RefCell::new(rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(42));
    // Function to create words from strs where terminals are split randomly.
    let mk_word = |s: &str| {
      Word::from_str_split_terminals(
        s,
        |c| {
          if ('N'..='Z').contains(&c) {
            Some(Variable { id: c as usize })
          } else {
            None
          }
        },
        |_, _| rng.borrow_mut().gen_bool(1.0 / 3.0),
      )
    };
    assert_eq!(mk_word(""), mk_word(""));
    // Generate some random words and test equality.
    for _ in 0..256 {
      let len = rng.borrow_mut().gen_range(0..8);
      let text = Alphanumeric.sample_string(&mut *rng.borrow_mut(), len);
      assert_eq!(mk_word(&text), mk_word(&text));
      if len > 0 {
        let not_equal_text = {
          let mut x = text.as_bytes().to_owned();
          let idx = rng.borrow_mut().gen_range(0..len);
          let old_c = x[idx];
          x[idx] = loop {
            let new_c = rng.borrow_mut().sample(Alphanumeric) as u8;
            if old_c != new_c {
              break new_c;
            }
          };
          String::from_utf8(x).unwrap()
        };
        assert_ne!(mk_word(&text), mk_word(&not_equal_text));
      }
    }
  }
}
