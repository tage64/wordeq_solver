use std::ops::ControlFlow::*;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering::*};

use super::{SearchTree, Splits};
use crate::*;

/// A node in the search tree together with its branches.
///
/// We keep track of which branches have been taken and which branches have been finished.
#[derive(Debug)]
pub struct Branches {
  /// The node from from which the branches are derived.
  pub node: SearchNode,
  /// The splits computed from `self.node`.
  pub splits: Splits,
  /// A set of all splits which have been taken by any thread. The elements are indices in the
  /// range `0..self.splits.len()`.
  pub taken_branches: AtomicBitSet,
  /// A set of all splits where the search is finished.
  pub finished_branches: AtomicBitSet,
  /// Set to true iff one thread has backtracked to the parent.
  ///
  /// Only one thread is allowed to backtrack to the parent. It'll be the first thread that sees
  /// `self.finished_branches` to contain all branches. But we need a lock to make sure that two
  /// threads doesn't set their respective branch's finish status at the same time and sees that
  /// all branches are finished at the same time.
  ///
  /// So after a thread sees that all branches are finished, it'll set `self.has_backtracked` to
  /// true with a swap operation and only if the old value was false it'll continue.
  has_backtracked: AtomicBool,
  /// The maximum for the non-reducing depth. Used for iterative deepening.
  pub non_reducing_max_depth: usize,
  /// A bool which is true iff any of the finished branches reached its max depth.
  ///
  /// We need to keep track of this. If this is false, then we can prove UNSAT.
  pub reached_max_depth: AtomicBool,
  /// A `(parent_branch_idx, parent_branches)` pair where `parent_branch_idx` is the branch index of
  /// the node and `parent_branches` is the parent of `self.node` together with its branches.
  pub parent: Option<(u32, Arc<Branches>)>,
}

/// A result from searching for a solution.
#[derive(Debug)]
pub enum SearchResult {
  /// A solution have been found: SAT, UNSAT or cancelled.
  ProvedSolution(Solution),
  /// The entire tree has been exhaustively searched to the max depth and no solution has been
  /// found.
  NoSolution,
  /// This thread completed its work but the search tree was not finished. Also returned when
  /// this thread was cancelled.
  DidntFinishSearch,
}
use SearchResult::*;

impl Branches {
  /// Create a new `Branches`.
  pub fn new(
    node: SearchNode,
    splits: Splits,
    non_reducing_max_depth: usize,
    parent: Option<(u32, Arc<Self>)>,
  ) -> Arc<Self> {
    Arc::new(Self {
      node,
      splits,
      non_reducing_max_depth,
      parent,
      taken_branches: AtomicBitSet::new(),
      finished_branches: AtomicBitSet::new(),
      has_backtracked: AtomicBool::new(false),
      reached_max_depth: AtomicBool::new(false),
    })
  }

  /// Search for a solution in all branches and backtrack to the parent when/if all branches are
  /// finished.
  ///
  /// If any branch is not taken, this function will take that branch. If even more branches are
  /// available, it will check if a thread is idle and send this `Branches` instance to that
  /// thread as well. In any case, this thread will exhaustively try to search through the
  /// branches.
  ///
  /// When all branches is taken, it will check if all branches are also finished. If not, some
  /// other thread is working on a branch and this thread will return `DidntFinishSearch` to signal
  /// to the runtime that it is available for new work. If however all branches are finished we
  /// will backtrack to the parent.
  ///
  /// This function is not recursive, but it is called recursively when it enters a new thread. And
  /// it could equally well be called recursively. We have chosen to make it non-recursive because
  /// we don't want to overflow the stack and keep the stack size small for the worker threads.
  pub fn search<W: NodeWatcher>(
    mut self: Arc<Self>,
    search_tree: &SearchTree<'_, W>,
  ) -> SearchResult {
    loop {
      // Check if we should stop this thread because some other thread found a solution.
      if search_tree.should_exit_search.load(Acquire) {
        return DidntFinishSearch;
      }
      // Select a branch, clone `self.node` and perform the split on that node. We do this in a
      // loop because if all branches are finished we backtrack (I.E change `self` to the parent).
      let (node, branch_idx) = loop {
        // Check if all branches are taken by some thread, otherwise take the first available
        // branch.
        if let Some(branch_idx) =
          self
            .taken_branches
            .set_first_available(self.splits.len(), AcqRel, Acquire)
        {
          // Check if this branch is non-reducing and set `non_reducing_depth` accordingly.
          let non_reducing_depth = if self.splits.is_reducing(branch_idx, &self.node) {
            self.node.non_reducing_depth
          } else {
            // Check if we reached max depth.
            if self.node.non_reducing_depth + 1 == self.non_reducing_max_depth {
              #[cfg(feature = "trace_logging")]
              log::trace!(
                "{:depth$}Max depth {} reached with this non reducing branch.",
                "",
                self.non_reducing_max_depth,
                depth = self.node.depth + 1,
              );
              self.reached_max_depth.store(true, Release);
              self.finished_branches.add(branch_idx, AcqRel);
              continue;
            }
            self.node.non_reducing_depth + 1
          };
          // If there are even more untaken branches and if there are idle threads, ask a thread
          // to cooperate on these branches.
          if !self
            .taken_branches
            .contains_all_below(self.splits.len(), Acquire)
          {
            let _ = search_tree.try_post_work(&self);
          }
          let mut node = self.node.clone();
          node.depth += 1;
          node.non_reducing_depth = non_reducing_depth;
          // Execute the branch / perform the split.
          let (branch_var, replacement) = self.splits.get(branch_idx);
          #[cfg(feature = "trace_logging")]
          log::trace!(
            "{:depth$}branching: {} = {}",
            "",
            &search_tree.original_formula.var_names[branch_var.id],
            display_word(replacement.iter(), |x| &search_tree
              .original_formula
              .var_names[x.id]),
            depth = node.depth,
          );
          node.fix_var(branch_var, replacement);
          break (node, branch_idx);
        } else {
          // All splits have been taken. If there are still threads working on splits, or if some
          // thread has already backtracked, we should return `DidntFinishSearch`, otherwise we
          // should backtrack to the parent.
          if self
            .finished_branches
            .contains_all_below(self.splits.len(), Acquire)
            && !self.has_backtracked.swap(true, AcqRel)
          {
            let Some((parent_branch_idx, parent_edge)) = self.parent.as_ref() else {
              // There is no parent so this is the root.
              if self.reached_max_depth.load(Acquire) {
                // If we reached max depth somewhere in the search we cannot no if there is a
                // solution so we can't prove UNSAT.
                return NoSolution;
              } else {
                return ProvedSolution(Unsat);
              }
            };
            // If we reached max depth in any branch we should set `reached_max_depth = true` for the
            // parent.
            parent_edge
              .reached_max_depth
              .fetch_or(self.reached_max_depth.load(Acquire), AcqRel);
            // Add `parent_branch_idx` to the parent's `finished_branches`.
            parent_edge
              .finished_branches
              .add(*parent_branch_idx, AcqRel);
            // Set the current node to the parent.
            self = parent_edge.clone();
            continue;
          }
          // All splits was taken but not all splits was finished so some other thread is still
          // working on this node. Or some other thread has already backtracked.
          return DidntFinishSearch;
        }
      };
      // Check if `node` is SAT, UNSAT, or create splits.
      match node.compute(search_tree.node_watcher, search_tree.original_formula) {
        Break(Unsat) => {
          self.finished_branches.add(branch_idx, AcqRel);
        }
        Break(x @ (Sat(_) | Cancelled)) => return ProvedSolution(x),
        Continue((node, splits)) => {
          // Take this branch and go one step deeper in the tree.
          self = Self::new(
            node,
            splits,
            self.non_reducing_max_depth,
            Some((branch_idx, self)),
          );
        }
      }
    }
  }
}
