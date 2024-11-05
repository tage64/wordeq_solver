#![expect(dead_code)]
use vec_map::VecMap;

use crate::*;

#[derive(Debug)]
pub struct AssignmentCache {
  assignments: Vec<Vec<(Variable, Word)>>,
}

impl AssignmentCache {
  pub fn new() -> Self {
    Self {
      assignments: Vec::new(),
    }
  }

  pub fn contains(&self, assignments: &VecMap<Word>) -> bool {
    self.assignments.iter().any(|x| {
      x.iter()
        .all(|(x, expected)| assignments.get(x.id) == Some(expected))
    })
  }

  pub fn add(&mut self, assignments: &VecMap<Word>) {
    let mut i = 0;
    while i < self.assignments.len() {
      if self.assignments[i]
        .iter()
        .all(|(x, expected)| assignments.get(x.id) == Some(expected))
      {
        self.assignments.swap_remove(i);
      } else {
        i += 1;
      }
    }
    self.assignments.push(
      assignments
        .iter()
        .map(|(id, word)| (Variable { id }, word.clone()))
        .collect(),
    );
  }
}
