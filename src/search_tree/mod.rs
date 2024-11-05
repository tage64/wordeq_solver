mod assignment_cache;
mod branches;
mod node;
pub mod solution;
mod splits;
use std::array;
use std::hint;
use std::num::NonZero;
use std::ops::ControlFlow::{self, *};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::*};
use std::sync::{Arc, Condvar, Mutex, RwLock};
use std::thread;

use assignment_cache::AssignmentCache;
use branches::{BranchStatus, Branches, SearchResult::*};
pub use node::SearchNode;
use splits::{SplitKind, Splits};

use crate::*;

const INITIAL_MAX_DEPTH: usize = 4;
const MAX_DEPTH_STEP: usize = 2;
const THREAD_STACK_SIZE: usize = 2usize.pow(25);

/// Simple solve function which doesn't use a watcher and only runs on one thread.
pub fn solve_simple(formula: Formula) -> Solution {
  solve(formula, dummy_watcher(), 1.try_into().unwrap()).0
}

/// Try to solve a formula.
///
/// Takes in a closure (node_watcher) which may cancel the search at any node by returning
/// `ControlFlow::Break(_)`. It will be called at every new node, right before the fix point
/// function.
pub fn solve<W: NodeWatcher>(
  formula: Formula,
  node_watcher: W,
  n_threads: NonZero<u32>,
) -> (Solution, W::Finished) {
  let shared_info = SharedInfo::new(formula, node_watcher);
  let solution = match SearchTree::create(&shared_info, n_threads) {
    Break(x) => x,
    Continue(search_tree) => search_tree.search(),
  };
  (solution, shared_info.node_watcher.finish())
}

/// Some common information and caches which are shared for all nodes in the search tree.
#[derive(Debug)]
struct SharedInfo<W> {
  /// The original formula which we are trying to solve.
  original_formula: Formula,
  node_watcher: W,
  /// A cache for assignments which we have proved lead to UNSAT.
  proved_unsat: RwLock<AssignmentCache>,
  /// A cache for assignment which we know that they don't have a solution until the current max
  /// depth.
  unknown_till_max_depth: RwLock<AssignmentCache>,
}

impl<W> SharedInfo<W> {
  fn new(formula: Formula, node_watcher: W) -> Self {
    Self {
      original_formula: formula,
      node_watcher,
      proved_unsat: RwLock::new(AssignmentCache::new()),
      unknown_till_max_depth: RwLock::new(AssignmentCache::new()),
    }
  }
}

/// A search tree. It takes care of managing all threads and performing the search.
///
/// See the documentation for individual fields for more details.
struct SearchTree<'a, W> {
  /// A reference to the node watcher.
  shared_info: &'a SharedInfo<W>,
  /// The max depth for non-reducing splits. We use iterative deepening so this will be updated
  /// from time to time.
  non_reducing_max_depth: AtomicUsize,
  /// The root node where `SearchNode.compute()` already has been run.
  root_node: SearchNode<'a, W>,
  /// The splits from the root node.
  root_splits: Splits,
  /// The number of threads.
  n_threads: NonZero<u32>,
  /// The threads that are currently not available to receive work.
  ///
  /// This is an atomic bit set, that is a set of integers which corresponds to thread indices.
  ///
  /// This is a superset of `self.busy_threads`. If a thread `i` is in this set but not in
  /// `busy_threads`, then we are currently storing its work in `posted_work[i]`. Think of
  /// `self.unavailable_threads[i]` and `self.busy_threads[i]` as a lock for `self.posted_work[i]`
  /// which is locked when the former is true and the latter is false.
  ///
  /// Note that this implies that when thread `i` has completed its work, it must remove itself
  /// from `self.busy_threads` before `self.available_threads`.
  unavailable_threads: AtomicBitSet,
  /// A set of the threads which are currently working.
  ///
  /// Each idle thread `i` waits in a busy loop for `busy_threads[i]` to be set. When that happens,
  /// it'll take its work from `posted_work[i]` and start working. When it becomes idle again,
  /// it'll remove itself from `self.busy_threads` and `self.available_threads`.
  busy_threads: AtomicBitSet,
  /// `posted_work[i]` contains the work to be done for thread `i`. This will only be set when
  /// thread `i` is idle (not in `self.unavailable_threads`), and thread `i` will take it as soon
  /// as possible.
  ///
  /// If `i` is not in `self.available_threads` or is in `self.busy_threads`,
  /// `self.posted_work[i]` is not initialized.
  posted_work: [Mutex<Option<Arc<Branches<'a, W>>>>; AtomicBitSet::MAX as usize],
  /// If any thread founds a solution, it will be put in this mutex and `self.solution_condvar`
  /// will be notified.
  solution: Mutex<Option<Solution>>,
  /// This condition variable will be notified when any thread founds a solution.
  solution_condvar: Condvar,
  /// This will be set to true when and only when a thread founds a solution, including that the
  /// node watcher cancels the solver. When this is true it signals to all threads to terminate as
  /// soon as possible.
  should_exit_search: AtomicBool,
}

impl<'a, W: NodeWatcher> SearchTree<'a, W> {
  /// Create a new search tree.
  ///
  /// This function will simplify and create the splits for the root node. This means that it may
  /// get a solution immediately if the root formula is obviously SAT or UNSAT, and hence it may
  /// return that result through the `Break` variant.
  fn create(
    shared_info: &'a SharedInfo<W>,
    n_threads: NonZero<u32>,
  ) -> ControlFlow<Solution, Self> {
    let (root_node, root_splits) =
      SearchNode::new(shared_info.original_formula.cnf.clone(), shared_info)
        .compute(None)
        .map_break(Option::unwrap)?;
    Continue(Self {
      shared_info,
      non_reducing_max_depth: AtomicUsize::new(INITIAL_MAX_DEPTH),
      root_node,
      root_splits,
      n_threads,
      unavailable_threads: AtomicBitSet::new(),
      busy_threads: AtomicBitSet::new(),
      posted_work: array::from_fn(|_| Mutex::new(None)),
      solution: Mutex::new(None),
      solution_condvar: Condvar::new(),
      should_exit_search: AtomicBool::new(false),
    })
  }

  /// Search for a solution until it is found or the node watcher signals that it should be
  /// cancelled.
  fn search(self) -> Solution {
    thread::scope(|scope| {
      // Launch all worker threads.
      for index in 0..self.n_threads.get() {
        let self_ = &self;
        thread::Builder::new()
          .name(format!("Solver thread {}", index + 1))
          .stack_size(THREAD_STACK_SIZE)
          .spawn_scoped(scope, move || self_.worker_thread(index))
          .unwrap();
      }

      // Send the root node to the first thread.
      self.try_post_work(&self.get_root()).unwrap();

      // Wait for the solution.
      let mut solution_guard = self.solution.lock().unwrap();
      loop {
        if let Some(res) = solution_guard.take() {
          break res;
        }
        solution_guard = self.solution_condvar.wait(solution_guard).unwrap();
      }
    })
  }

  /// Get the branches for the root node.
  fn get_root(&self) -> Arc<Branches<'a, W>> {
    Branches::new(
      self.root_node.clone(),
      self.root_splits.clone(),
      self.non_reducing_max_depth.load(Acquire),
      None,
    )
  }

  /// Given some branches in the search tree, try to post them to an idle thread.
  ///
  /// If no thread is idle, this method will return `Err(())` and the `Arc` will not be cloned.
  fn try_post_work(&self, branches: &Arc<Branches<'a, W>>) -> Result<(), ()> {
    // Check if any thread is idle.
    let Some(index) =
      self
        .unavailable_threads
        .set_first_available(self.n_threads.get(), AcqRel, Acquire)
    else {
      return Err(());
    };
    let mut lock = self.posted_work[index as usize].try_lock().unwrap();
    assert!(lock.is_none());
    *lock = Some(branches.clone());
    drop(lock);
    // Mark the thread as busy. The spin loop in the thread will recognize this and the thread will
    // start working after this is set.
    self.busy_threads.add(index, AcqRel);
    Ok(())
  }

  /// Function run in each worker thread for the solver.
  ///
  /// It roughly works as follows, (asuming that the thread index is `i`):
  /// 1. Wait in a spin loop for some work. That is until `self.busy_threads[i]` is true.
  ///   1.1. In the loop, also check if `self.should_exit_search` is true and terminate the thread
  ///     in that case.
  /// 2. Take the work (an instance of `Arc<Branches>`) from `self.posted_work[i]`.
  /// 3. Run the search method `Branches::search()`.
  ///   a) If it returns a solution, set `self.should_exit_search` to true and store the result in
  ///   `self.solution`. Terminate the thread.
  ///   b) If it returns `NoSolution` increase the max depth and run step 3 again.
  ///   c) If it returns `DidntFinishSearch`, put the thread in idle mode and go back to step 1.
  fn worker_thread(&self, index: u32) {
    log::trace!("Launched thread {}", index + 1);
    loop {
      // Busy waiting until someone posts a job on this thread.
      while !self.busy_threads.contains(index, Acquire) {
        hint::spin_loop();
        if self.should_exit_search.load(Acquire) {
          return;
        }
      }
      #[cfg(feature = "trace_logging")]
      log::trace!("Thread {} got work", index + 1);
      // Take the work.
      let mut branches = self.posted_work[index as usize]
        .lock()
        .unwrap()
        .take()
        .unwrap();
      loop {
        match branches.search(self) {
          ProvedSolution(x) => {
            #[cfg(feature = "trace_logging")]
            log::trace!("Thread {} got result {x}", index + 1);
            self.should_exit_search.store(true, Release);
            self.solution.lock().unwrap().get_or_insert(x);
            self.solution_condvar.notify_all();
            return;
          }
          NoSolution => {
            // Increase max depth.
            self
              .non_reducing_max_depth
              .fetch_add(MAX_DEPTH_STEP, AcqRel);
            #[cfg(feature = "trace_logging")]
            log::trace!(
              "Thread {} increased max depth to {}",
              index + 1,
              self.non_reducing_max_depth.load(Acquire)
            );
            branches = self.get_root();
          }
          DidntFinishSearch => {
            // Set this thread to be available.
            #[cfg(feature = "trace_logging")]
            log::trace!(
              "Thread {} didn't finish search and is waiting for job.",
              index + 1
            );
            self.busy_threads.remove(index, AcqRel);
            self.unavailable_threads.remove(index, AcqRel);
            break;
          }
        }
      }
    }
  }
}
