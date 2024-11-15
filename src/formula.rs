mod eq_parser;
use std::collections::HashMap;
use std::fmt;
use std::mem;

use allocator_api2::alloc::{Allocator, Global};
use arrayvec::ArrayVec;
use compact_str::CompactString;
use serde::{Deserialize, Serialize};

use crate::{AtomicBitSet, vec_list::VecList};

/// The maximum length of a terminal.
const TERMINAL_MAX_LEN: usize = AtomicBitSet::MAX as usize;

/// A terminal (a character).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Terminal(pub ArrayVec<u8, TERMINAL_MAX_LEN>);

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
  Terminal(&'a [u8]),
  Variable(Variable),
}

/// A word is a list of terms.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound(deserialize = "A:Default", serialize = ""))]
pub struct Word<A: Allocator = Global>(pub VecList<Term, A>);

/// An equality constraint.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound(deserialize = "A:Default", serialize = ""))]
pub struct Equation<A: Allocator = Global> {
  pub lhs: Word<A>,
  pub rhs: Word<A>,
}

/// A side in an equation, LHS or RHS.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Side {
  Lhs,
  Rhs,
}
pub use Side::*;

/// A clause in a conjunction.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound(deserialize = "A:Default", serialize = ""))]
pub struct Clause<A: Allocator = Global> {
  /// This could be extended to be disjunction and negations but it is only an equation for now.
  pub equation: Equation<A>,
}

/// A list of clauses.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound(deserialize = "A:Default", serialize = ""))]
pub struct Cnf<A: Allocator = Global>(pub VecList<Clause<A>, A>);

/// A formula.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound(deserialize = "A:Default", serialize = ""))]
pub struct Formula<A: Allocator = Global> {
  pub(crate) cnf: Cnf<A>,
  pub(crate) var_names: Vec<CompactString>,
  pub(crate) terminal_chars: Vec<char>,
}

impl Term {
  fn borrow(&self) -> BorrowedTerm<'_> {
    match self {
      Term::Variable(x) => BorrowedTerm::Variable(*x),
      Term::Terminal(Terminal(s)) => BorrowedTerm::Terminal(&s),
    }
  }
}

impl Word {
  pub fn from_str(
    text: &str,
    mut get_var: impl FnMut(char) -> Option<Variable>,
    mut get_terminal: impl FnMut(char) -> u8,
  ) -> Word {
    let mut word = Word(VecList::new());
    let mut curr_word_terminal = ArrayVec::new();
    for c in text.chars() {
      let maybe_var = get_var(c);
      if !curr_word_terminal.is_empty() && (maybe_var.is_some() || curr_word_terminal.is_full()) {
        word.0.insert_back(Term::Terminal(Terminal(mem::replace(
          &mut curr_word_terminal,
          Default::default(),
        ))));
      }
      if let Some(var) = maybe_var {
        word.0.insert_back(Term::Variable(var));
      } else {
        curr_word_terminal.push(get_terminal(c));
      }
    }
    if !curr_word_terminal.is_empty() {
      word
        .0
        .insert_back(Term::Terminal(Terminal(curr_word_terminal)));
    }
    word
  }
}

impl<A: Allocator> Word<A> {
  /// Clone the word with a new allocator.
  pub fn clone_in<B: Allocator>(&self, alloc: B) -> Word<B> {
    Word(self.0.clone_map_in(|x| x.clone(), alloc))
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

impl<A: Allocator> Equation<A> {
  /// Get a side of the equation.
  pub fn side(&self, side: Side) -> &Word<A> {
    let Self { lhs, rhs } = self;
    match side {
      Lhs => lhs,
      Rhs => rhs,
    }
  }

  /// Clone the equation with a new allocator.
  pub fn clone_in<B: Allocator + Copy>(&self, alloc: B) -> Equation<B> {
    Equation {
      lhs: self.lhs.clone_in(alloc),
      rhs: self.rhs.clone_in(alloc),
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

impl<A: Allocator> Clause<A> {
  /// Clone the clause with a new allocator.
  pub fn clone_in<B: Allocator + Copy>(&self, alloc: B) -> Clause<B> {
    Clause {
      equation: self.equation.clone_in(alloc),
    }
  }
}

impl Formula {
  pub fn new(cnf: Cnf, var_names: Vec<CompactString>, terminal_chars: Vec<char>) -> Self {
    Self {
      cnf,
      var_names,
      terminal_chars,
    }
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
    let mut used_terminals = HashMap::<char, u8>::new(); // Terminals and there assigned numbers.
    let mut get_terminal = |c: char| {
      let next_terminal_id = used_terminals.len();
      *used_terminals
        .entry(c)
        .or_insert(next_terminal_id.try_into().expect(
          "Too many different terminals. Currently we only support 256 different terminals in a \
           formula.",
        ))
    };
    let mut cnf = Cnf(VecList::with_capacity(equations.len()));
    for (text_lhs, text_rhs) in equations {
      let lhs = Word::from_str(text_lhs, &mut get_var, &mut get_terminal);
      let rhs = Word::from_str(text_rhs, &mut get_var, &mut get_terminal);
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
    let mut terminal_names = used_terminals.keys().copied().collect::<Vec<char>>();
    terminal_names.sort_unstable_by_key(|x| used_terminals[x]);
    Self::new(cnf, var_names, terminal_names)
  }

  /// Parse a .eq file.
  pub fn from_eq_file(text: &str) -> anyhow::Result<Self> {
    eq_parser::EqParser::parse_to_formula(text)
  }

  /// The number of variables in this formula.
  pub fn no_vars(&self) -> usize {
    self.var_names.len()
  }

  /// Display a word in this formula.
  pub fn display_word<'a, W>(&'a self, word: W) -> impl fmt::Display + use<'a, W>
  where
    W: IntoIterator<Item = &'a Term> + Clone,
  {
    struct Displayer<'a, W>(&'a Formula, W);
    impl<'a, W> fmt::Display for Displayer<'a, W>
    where
      W: IntoIterator<Item = &'a Term> + Clone,
    {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for term in self.1.clone() {
          match term {
            Term::Terminal(Terminal(t)) => {
              for x in t.iter() {
                write!(f, "{}", self.0.terminal_chars[*x as usize])?
              }
            }
            Term::Variable(Variable { id }) => write!(f, "{}", self.0.var_names[*id])?,
          }
        }
        Ok(())
      }
    }
    Displayer(self, word)
  }
}

impl fmt::Display for Formula {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    for (clause_ptr, clause) in self.cnf.0.iter() {
      write!(
        f,
        "{}",
        self.display_word(clause.equation.lhs.0.iter().map(|(_, x)| x))
      )?;
      write!(f, " = ")?;
      write!(
        f,
        "{}",
        self.display_word(clause.equation.rhs.0.iter().map(|(_, x)| x))
      )?;
      if clause_ptr != self.cnf.0.back().unwrap() {
        write!(f, "; ")?;
      }
    }
    Ok(())
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
      Word::from_str(
        s,
        |c| {
          if ('N'..='Z').contains(&c) {
            Some(Variable { id: c as usize })
          } else {
            None
          }
        },
        |c| c as u8,
      )
    };
    assert_eq!(mk_word(""), mk_word(""));
    // Generate some random words and test equality.
    for _ in 0..256 {
      let len = rng.borrow_mut().gen_range(0..TERMINAL_MAX_LEN * 2 + 2);
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
