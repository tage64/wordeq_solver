/// A bit set with a single usize as backing storage.
#[derive(Debug, Clone, Copy)]
pub struct BitSetUsize(usize);

impl BitSetUsize {
  pub const MAX: u32 = usize::BITS;

  /// Create a empty empty bit set.
  #[inline(always)]
  pub fn empty() -> Self {
    BitSetUsize(0)
  }

  /// Checks if a number is contained in the set.
  pub fn contains(&self, x: u32) -> bool {
    debug_assert!(x < Self::MAX);
    (self.0 & 1 << x) != 0
  }

  /// Complement this set.
  #[inline(always)]
  pub fn complement(&mut self) -> &mut Self {
    self.0 = !self.0;
    self
  }

  /// Add a number to the ste.
  #[inline(always)]
  pub fn add(&mut self, x: u32) -> &mut Self {
    debug_assert!(x < Self::MAX);
    self.0 |= 1 << x;
    self
  }

  /// Set self to be the union of self and other.
  pub fn add_all(&mut self, other: &Self) -> &mut Self {
    self.0 |= other.0;
    self
  }

  /// Remove a number from the set if present.
  #[inline(always)]
  pub fn remove(&mut self, x: u32) -> &mut Self {
    debug_assert!(x < Self::MAX);
    self.0 &= !(1 << x);
    self
  }
}

#[cfg(test)]
mod tests {
  use std::array;

  use rand::prelude::*;

  use super::*;

  #[test]
  fn bit_set_usize_random_tests() {
    let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(42);
    let mut bitset = BitSetUsize::empty();
    let mut reference_set = [false; BitSetUsize::MAX as usize];
    for _ in 0..1024 {
      match rng.gen_range(0..3) {
        0 => {
          let x = rng.gen_range(0..BitSetUsize::MAX);
          bitset.add(x);
          reference_set[x as usize] = true;
        }
        1 => {
          let x = rng.gen_range(0..BitSetUsize::MAX);
          bitset.remove(x);
          reference_set[x as usize] = false;
        }
        2 => {
          bitset.complement();
          reference_set = array::from_fn(|i| !reference_set[i]);
        }
        _ => unreachable!(),
      }
      for (i, x) in reference_set.iter().copied().enumerate() {
        assert_eq!(x, bitset.contains(i as u32));
      }
    }
  }
}
