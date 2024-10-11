use std::ops::ControlFlow;
use std::time::{Duration, Instant};

use derive_more::Display;
use humantime::format_duration;
use serde::{Deserialize, Serialize};

pub trait NodeWatcher {
  /// This method should be called at each node. If ite returns `ControlFlow::Break(())`, the
  /// search should exit with `Cancelled`.
  fn visit_node(&mut self) -> ControlFlow<()>;
}

/// Create a node watcher from a function.
pub fn watch_fn(f: impl FnMut() -> ControlFlow<()>) -> impl NodeWatcher {
  struct Watcher<F>(F);
  impl<F: FnMut() -> ControlFlow<()>> NodeWatcher for Watcher<F> {
    #[inline]
    fn visit_node(&mut self) -> ControlFlow<()> {
      (self.0)()
    }
  }
  Watcher(f)
}

pub fn dummy_watcher() -> impl NodeWatcher {
  watch_fn(|| ControlFlow::Continue(()))
}

#[derive(Debug)]
pub struct Timeout {
  pub start: Instant,
  pub timeout: Duration,
}

impl Timeout {
  pub fn from_now(timeout: Duration) -> Self {
    Self {
      start: Instant::now(),
      timeout,
    }
  }
}

impl NodeWatcher for Timeout {
  fn visit_node(&mut self) -> ControlFlow<()> {
    if self.start.elapsed() > self.timeout {
      ControlFlow::Break(())
    } else {
      ControlFlow::Continue(())
    }
  }
}

/// Statistics about a search. Retrieved from the `CollectNodeStats` watcher.
#[derive(Debug, Clone, Display, Serialize, Deserialize)]
#[display(
  "{node_count} nodes in {}. Mean node time: {}.",
  format_duration(self.search_time),
  format_duration(self.search_time/self.node_count.try_into().unwrap())
)]
pub struct NodeStats {
  pub node_count: usize,
  pub search_time: Duration,
}

/// A watcher which collects statistics about the number of nodes and related information.
#[derive(Debug)]
pub struct CollectNodeStats {
  timeout: Timeout,
  node_count: usize,
}

impl CollectNodeStats {
  /// Start the timers now.
  pub fn from_now(timeout: Duration) -> Self {
    Self {
      timeout: Timeout::from_now(timeout),
      node_count: 0,
    }
  }

  /// Call this immediately after the solver is finished to get correct times.
  pub fn finished(self) -> NodeStats {
    NodeStats {
      node_count: self.node_count,
      search_time: self.timeout.start.elapsed(),
    }
  }
}

impl NodeWatcher for CollectNodeStats {
  fn visit_node(&mut self) -> ControlFlow<()> {
    self.node_count += 1;
    self.timeout.visit_node()
  }
}
