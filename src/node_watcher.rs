use std::ops::ControlFlow;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use derive_more::Display;
use serde::{Deserialize, Serialize};

use crate::*;
//use memory_stats::memory_stats;

pub trait NodeWatcher: Send + Sync + Sized {
  /// Type which the watcher should be converted to when it is finished.
  type Finished;

  /// This method should be called before each node. If it returns `ControlFlow::Break(())`, the
  /// search should exit with `Cancelled`. Note that this method may be called after it has
  /// returned `Break` due to multiple threads.
  fn visit_node(&self, solver: &SearchNode<Self>) -> ControlFlow<()>;

  /// Call this each time the max depth is updated, including at the beginning. Will only be called
  /// with successively larger values.
  fn increase_max_depth(&self, _max_depth: usize) {}

  /// Called when the search is finished.
  fn finish(self) -> Self::Finished;
}

/// Create a node watcher from a function.
pub fn watch_fn(f: impl Fn() -> ControlFlow<()> + Send + Sync) -> impl NodeWatcher {
  struct Watcher<F>(F);
  impl<F: Fn() -> ControlFlow<()> + Send + Sync> NodeWatcher for Watcher<F> {
    type Finished = ();
    #[inline]
    fn visit_node(&self, _: &SearchNode<Self>) -> ControlFlow<()> {
      (self.0)()
    }
    fn finish(self) -> () {}
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
  type Finished = ();
  fn visit_node(&self, _: &SearchNode<Self>) -> ControlFlow<()> {
    if self.start.elapsed() > self.timeout {
      ControlFlow::Break(())
    } else {
      ControlFlow::Continue(())
    }
  }
  fn finish(self) -> () {}
}

/// Statistics about a search. Retrieved from the `CollectNodeStats` watcher.
#[derive(Debug, Clone, Display, Serialize, Deserialize)]
#[display(
  "{node_count} nodes in {}. Mean node time: {}, startup time {}, max depth: {}.",
  format_duration(self.total_time()),
  format_duration(self.search_time/self.node_count.try_into().unwrap()),
  format_duration(self.startup_time),
  self.max_depth,
)]
pub struct NodeStats {
  /// The number of visited nodes.
  pub node_count: usize,
  /// The time between the initialization of the watcher and the first node was visited.
  ///
  /// This time typically includes the time to spawn all threads.
  pub startup_time: Duration,
  /// The time from the first node to till the search was finished.
  pub search_time: Duration,
  pub max_depth: usize,
  // Some out commented features follow.
  //pub max_physical_mem: f64,
  //pub max_virtual_mem: f64,
}

/// A watcher which collects statistics about the number of nodes and related information.
#[derive(Debug)]
pub struct CollectNodeStats {
  /// The timestamp when the search started.
  start: Instant,
  /// The pre-set timeout for the search.
  timeout: Duration,
  /// The number of visited nodes.
  node_count: AtomicUsize,
  /// The time between the start and the first visited node.
  startup_time: OnceLock<Duration>,
  max_depth: AtomicUsize,
  last_print_time: Mutex<Instant>,
  print_interval: Option<Duration>,
  // Out commented feature:
  //mem_use: Arc<Mutex<Option<(f64, f64)>>>,
}

impl CollectNodeStats {
  /// Start the timers now.
  pub fn from_now(timeout: Duration, print_stats_interval: Option<Duration>) -> Self {
    /* Out commented feature:
      let mem_use = Arc::new(Mutex::new(Some((0.0, 0.0))));
      let mem_use_ = mem_use.clone();
      thread::spawn(move || {
        loop {
          thread::sleep(Duration::from_millis(10));
          if let Some((max_physical, max_virtual)) = mem_use_.lock().unwrap().as_mut() {
            let stats = memory_stats().unwrap();
            if stats.physical_mem as f64 / 1000000.0 > *max_physical {
              *max_physical = stats.physical_mem as f64 / 1000000.0;
              //log::trace!("Max physical mem: {max_physical} MB");
            }
            if stats.virtual_mem as f64 / 1000000.0 > *max_virtual {
              *max_virtual = stats.virtual_mem as f64 / 1000000.0;
              //log::trace!("Max virtual mem: {max_physical} MB");
            }
          } else {
            break;
          }
        }
      });
    */

    let start = Instant::now();
    Self {
      start,
      timeout,
      node_count: AtomicUsize::new(0),
      max_depth: AtomicUsize::new(0),
      startup_time: OnceLock::new(),
      last_print_time: Mutex::new(start),
      print_interval: print_stats_interval,
    }
  }
}

impl NodeWatcher for CollectNodeStats {
  type Finished = NodeStats;

  fn visit_node(&self, solver: &SearchNode<Self>) -> ControlFlow<()> {
    let running_time = self.start.elapsed();
    if 0 == self.node_count.fetch_add(1, Ordering::Relaxed) {
      let _ = self.startup_time.set(running_time);
    }
    if let Some(print_interval) = self.print_interval {
      {
        let mut solver_sizes = solver.get_sizes();
        let solver_size = solver_sizes.iter().map(|x| x.1).sum::<usize>();
        {
          let mut last_print_time = self.last_print_time.lock().unwrap();
          if last_print_time.elapsed() >= print_interval {
            solver_sizes.sort_by_key(|(_, x)| *x);
            for (item, size) in solver_sizes {
              log::trace!("- {item}: {size} B");
            }
            log::trace!("Max solver size {solver_size} B.",);
            *last_print_time = Instant::now();
          }
        }
      }
    }
    if running_time > self.timeout {
      ControlFlow::Break(())
    } else {
      ControlFlow::Continue(())
    }
  }

  fn increase_max_depth(&self, max_depth: usize) {
    self.max_depth.store(max_depth, Ordering::Relaxed);
  }

  fn finish(self) -> NodeStats {
    let startup_time = *self.startup_time.get().unwrap();
    let search_time = self.start.elapsed() - startup_time;
    //let (max_physical_mem, max_virtual_mem) = self.mem_use.lock().unwrap().take().unwrap();
    NodeStats {
      search_time,
      startup_time,
      node_count: self.node_count.into_inner(),
      max_depth: self.max_depth.into_inner(),
      //max_physical_mem,
      //max_virtual_mem,
    }
  }
}

impl NodeStats {
  /// Get the total time. I.E startup time + search time.
  pub fn total_time(&self) -> Duration {
    self.startup_time + self.search_time
  }
}
