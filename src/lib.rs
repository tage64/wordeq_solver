mod atomic_bit_set;
pub mod benchmarks;
mod format_duration;
mod formula;
mod node_watcher;
mod search_tree;
pub mod vec_list;

use atomic_bit_set::AtomicBitSet;
use format_duration::format_duration;
pub use formula::*;
pub use node_watcher::*;
pub use search_tree::{SearchNode, solution::*, solve, solve_simple};

const INITIAL_MAX_DEPTH: usize = 4;
const MAX_DEPTH_STEP: usize = 2;
const THREAD_STACK_SIZE: usize = 2usize.pow(8);
