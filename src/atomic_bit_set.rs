use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Debug, Default)]
pub struct AtomicBitSet(AtomicUsize);

impl AtomicBitSet {
  pub const MAX: u32 = usize::BITS;

  /// Create a new empty bit set.
  pub fn new() -> Self {
    Self::default()
  }

  /// Check if the set contains an integer `x`. `x` must be in the range `0..Self::MAX`.
  pub fn contains(&self, x: u32, order: Ordering) -> bool {
    debug_assert!(x < Self::MAX);
    (self.0.load(order) & (1 << x)) != 0
  }

  /// Add an integer `x` to the set. `x` must be in the range `0..Self::MAX`.
  pub fn add(&self, x: u32, order: Ordering) {
    debug_assert!(x < Self::MAX);
    self.0.fetch_or(1 << x, order);
  }

  /// Remove an integer `x` from the set. `x` must be in the range `0..Self::MAX`.
  pub fn remove(&self, x: u32, order: Ordering) {
    debug_assert!(x < Self::MAX);
    self.0.fetch_and(!(1 << x), order);
  }

  /// Check if all integers smaller than an integer is in the set. `below` must be in the range
  /// `0..=Self::MAX`.
  pub fn contains_all_below(&self, below: u32, order: Ordering) -> bool {
    debug_assert!(below <= Self::MAX);
    self.0.load(order).trailing_ones() >= below
  }

  /// Set the smallest integer in the range 0..n which is not currently in the set. Returns the
  /// integer on success or None if the range was all set. `below` must be in the range
  /// `0..=Self::MAX`.
  pub fn set_first_available(
    &self,
    below: u32,
    set_order: Ordering,
    fetch_order: Ordering,
  ) -> Option<u32> {
    debug_assert!(
      below <= Self::MAX,
      "Argument below is {below}, must be <= {}",
      Self::MAX
    );
    let mut prev = self.0.load(fetch_order);
    loop {
      let index = prev.trailing_ones();
      if index >= below {
        return None;
      }
      let next = prev | (1 << index);
      match self
        .0
        .compare_exchange_weak(prev, next, set_order, fetch_order)
      {
        Ok(_) => return Some(index),
        Err(next_prev) => prev = next_prev,
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use Ordering::*;
  use rand::prelude::*;

  use super::*;

  #[test]
  fn test_atomic_bit_set_add_remove_contains() {
    let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(42);
    let bitset = AtomicBitSet::new();
    let mut reference = [false; AtomicBitSet::MAX as usize];
    for _ in 0..256 {
      let x = rng.gen_range(0..(AtomicBitSet::MAX));
      if rng.gen() {
        bitset.add(x, Relaxed);
        reference[x as usize] = true;
      } else {
        bitset.remove(x, Relaxed);
        reference[x as usize] = false;
      }
      for y in 0..AtomicBitSet::MAX {
        assert_eq!(bitset.contains(y, Relaxed), reference[y as usize],);
      }
    }
  }

  #[test]
  fn test_atomic_bit_set_contains_all_below() {
    let bitset = AtomicBitSet::new();
    assert!(bitset.contains_all_below(0, Relaxed));
    assert!(!bitset.contains_all_below(1, Relaxed));
    assert!(!bitset.contains_all_below(AtomicBitSet::MAX, Relaxed));
    bitset.add(2, Relaxed);
    assert!(bitset.contains_all_below(0, Relaxed));
    for i in 1..5 {
      assert!(!bitset.contains_all_below(i, Relaxed));
    }
    bitset.add(0, Relaxed);
    assert!(bitset.contains_all_below(0, Relaxed));
    assert!(bitset.contains_all_below(1, Relaxed));
    for i in 2..5 {
      assert!(!bitset.contains_all_below(i, Relaxed));
    }
    bitset.add(1, Relaxed);
    for i in 0..=3 {
      assert!(bitset.contains_all_below(i, Relaxed));
    }
    for i in 4..=AtomicBitSet::MAX {
      assert!(!bitset.contains_all_below(i, Relaxed));
    }
  }

  #[test]
  fn test_atomic_bit_set_contains_set_first_available() {
    let bitset = AtomicBitSet::new();
    for n in 0..AtomicBitSet::MAX {
      assert_eq!(None, bitset.set_first_available(n, Relaxed, Relaxed));
      assert_eq!(Some(n), bitset.set_first_available(n + 1, Relaxed, Relaxed));
      assert!(bitset.contains_all_below(n + 1, Relaxed),);
      if n + 2 <= AtomicBitSet::MAX {
        assert!(!bitset.contains_all_below(n + 2, Relaxed),);
      }
    }

    let bitset = AtomicBitSet::new();
    bitset.add(2, Relaxed);
    assert_eq!(Some(0), bitset.set_first_available(8, Relaxed, Relaxed));
    assert!(!bitset.contains_all_below(3, Relaxed));
    assert_eq!(Some(1), bitset.set_first_available(2, Relaxed, Relaxed));
    assert!(bitset.contains_all_below(3, Relaxed));
  }
}
