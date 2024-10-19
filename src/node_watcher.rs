use std::ops::ControlFlow;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use derive_more::Display;
use memory_stats::memory_stats;
use serde::{Deserialize, Serialize};

use crate::format_duration;

pub trait NodeWatcher: Send + Sync {
  /// This method should be called at each node. If ite returns `ControlFlow::Break(())`, the
  /// search should exit with `Cancelled`.
  fn visit_node(&self) -> ControlFlow<()>;
}

/// Create a node watcher from a function.
pub fn watch_fn(f: impl Fn() -> ControlFlow<()> + Send + Sync) -> impl NodeWatcher {
  struct Watcher<F>(F);
  impl<F: Fn() -> ControlFlow<()> + Send + Sync> NodeWatcher for Watcher<F> {
    #[inline]
    fn visit_node(&self) -> ControlFlow<()> {
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
  fn visit_node(&self) -> ControlFlow<()> {
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
  pub max_physical_mem: f64,
  pub max_virtual_mem: f64,
}

/// A watcher which collects statistics about the number of nodes and related information.
#[derive(Debug)]
pub struct CollectNodeStats {
  start: Instant,
  timeout: Option<Duration>,
  node_count: AtomicUsize,
  mem_use: Arc<Mutex<Option<(f64, f64)>>>,
}

impl CollectNodeStats {
  /// Start the timers now.
  pub fn from_now(timeout: Option<Duration>) -> Self {
    let mem_use = Arc::new(Mutex::new(Some((0.0, 0.0))));
    let mem_use_ = mem_use.clone();
    thread::spawn(move || {
      loop {
        thread::sleep(Duration::from_millis(10));
        if let Some((max_physical, max_virtual)) = mem_use_.lock().unwrap().as_mut() {
          let stats = memory_stats().unwrap();
          if stats.physical_mem as f64 / 1000000.0 > *max_physical {
            *max_physical = stats.physical_mem as f64 / 1000000.0;
            log::trace!("Max physical mem: {max_physical} MB");
          }
          if stats.virtual_mem as f64 / 1000000.0 > *max_virtual {
            *max_virtual = stats.virtual_mem as f64 / 1000000.0;
            log::trace!("Max virtual mem: {max_physical} MB");
          }
        } else {
          break;
        }
      }
    });
    Self {
      start: Instant::now(),
      timeout,
      node_count: AtomicUsize::new(0),
      mem_use,
    }
  }

  /// Call this immediately after the solver is finished to get correct times.
  pub fn finished(self) -> NodeStats {
    let search_time = self.start.elapsed();
    let (max_physical_mem, max_virtual_mem) = self.mem_use.lock().unwrap().take().unwrap();
    NodeStats {
      search_time,
      node_count: self.node_count.into_inner(),
      max_physical_mem,
      max_virtual_mem,
    }
  }
}

impl NodeWatcher for CollectNodeStats {
  fn visit_node(&self) -> ControlFlow<()> {
    self.node_count.fetch_add(1, Ordering::Relaxed);
    if let Some(timeout) = self.timeout {
      if self.start.elapsed() > timeout {
        ControlFlow::Break(())
      } else {
        ControlFlow::Continue(())
      }
    } else {
      ControlFlow::Continue(())
    }
  }
}
