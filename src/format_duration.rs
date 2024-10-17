use std::fmt;
use std::time::Duration;

/// Round a duration tto two significant digits and format it with an appropriate suffix.
pub fn format_duration(duration: Duration) -> impl fmt::Display {
  struct Displayer(Duration);
  impl fmt::Display for Displayer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      if self.0.is_zero() {
        write!(f, "0.0 ns")
      } else {
        let nanos = self.0.as_nanos();
        match nanos.ilog10() {
          (0..=2) => write!(f, "{nanos}ns"),
          (3..=4) => write!(f, "{}us", nanos as f64 / 1000.0),
          (5..=7) => write!(f, "{}ms", nanos as f64 / 1000000.0),
          _ => write!(f, "{}s", self.0.as_secs_f64()),
        }
      }
    }
  }
  Displayer(round_duration(duration, 2))
}

/// Round a duration to the specific number of significant figures.
fn round_duration(duration: Duration, figures: u32) -> Duration {
  if figures == 0 {
    return duration;
  }
  let nanos = duration.as_nanos();
  let rounded_nanos = if let Some(log) = nanos.checked_ilog10() {
    let mod_ = 10u128.pow(log.saturating_sub(figures - 1));
    let rem = nanos % mod_;
    if rem * 2 >= mod_ {
      nanos - rem + mod_
    } else {
      nanos - rem
    }
  } else {
    nanos
  };
  Duration::new(
    (rounded_nanos / 1000000000).try_into().unwrap(),
    (rounded_nanos % 1000000000).try_into().unwrap(),
  )
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_round_duration() {
    assert_eq!(
      Duration::from_nanos(0),
      round_duration(Duration::from_nanos(0), 2)
    );
    assert_eq!(
      Duration::from_nanos(3),
      round_duration(Duration::from_nanos(3), 2)
    );
    assert_eq!(
      Duration::from_nanos(32),
      round_duration(Duration::from_nanos(32), 2)
    );
    assert_eq!(
      Duration::from_nanos(330),
      round_duration(Duration::from_nanos(326), 2)
    );
    assert_eq!(
      Duration::from_nanos(1000),
      round_duration(Duration::from_nanos(1032), 2)
    );
    assert_eq!(
      Duration::from_millis(1200),
      round_duration(Duration::from_millis(1200), 2)
    );
  }
}
