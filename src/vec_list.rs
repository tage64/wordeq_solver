//! An implementation of a doubly linked list where all items are stored in a `Vec`.

use std::fmt;
use std::mem;

use allocator_api2::{
  alloc::{Allocator, Global},
  vec::Vec,
};
use nonmax::NonMaxUsize;
use serde::{Deserialize, Serialize};

/// A pointer to an element in a list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ListPtr(NonMaxUsize);

/// Assert that an option of a pointer has size of usize.
const _: () = assert!(mem::size_of::<Option<ListPtr>>() == mem::size_of::<usize>());

impl ListPtr {
  /// Get a usize for this pointer.
  pub fn to_usize(self) -> usize {
    self.0.get()
  }

  /// Create a pointer from a usize. The usize must have been created by the
  /// `ListPtr::to_usize()` method.
  pub fn from_usize(x: usize) -> Self {
    ListPtr(NonMaxUsize::new(x).unwrap())
  }
}

/// An occupied entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct OccupiedEntry<T> {
  item: T,
  prev: Option<ListPtr>,
  next: Option<ListPtr>,
}

/// An entry in a list.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Entry<T> {
  Occupied(OccupiedEntry<T>),
  Vacant {
    /// The next vacant entry.
    next_vacant: Option<ListPtr>,
  },
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(bound(
  deserialize = "T: Deserialize<'de>, A: Default",
  serialize = "T: Serialize"
))]
pub struct VecList<T, A: Allocator = Global> {
  entries: Vec<Entry<T>, A>,
  head: Option<ListPtr>,
  back: Option<ListPtr>,
  vacant_head: Option<ListPtr>,
  len: usize,
}

impl<T> VecList<T> {
  /// Create a new empty list.
  pub fn new() -> Self {
    Self {
      entries: Vec::new(),
      head: None,
      back: None,
      vacant_head: None,
      len: 0,
    }
  }

  /// Create a new empty list with a capacity.
  pub fn with_capacity(cap: usize) -> Self {
    Self {
      entries: Vec::with_capacity(cap),
      head: None,
      back: None,
      vacant_head: None,
      len: 0,
    }
  }
}

impl<T, A: Allocator> VecList<T, A> {
  /// Create a new empty list.
  pub fn new_in(alloc: A) -> Self {
    Self {
      entries: Vec::new_in(alloc),
      head: None,
      back: None,
      vacant_head: None,
      len: 0,
    }
  }

  /// Create a new empty list with a capacity.
  pub fn with_capacity_in(cap: usize, alloc: A) -> Self {
    Self {
      entries: Vec::with_capacity_in(cap, alloc),
      head: None,
      back: None,
      vacant_head: None,
      len: 0,
    }
  }

  /// Clone the list with a map function and a new allocator.
  pub fn clone_map_in<U, B: Allocator>(
    &self,
    mut clone_item: impl FnMut(&T) -> U,
    alloc: B,
  ) -> VecList<U, B> {
    let mut entries = Vec::with_capacity_in(self.entries.len(), alloc);
    entries.extend(self.entries.iter().map(|entry| match entry {
      Entry::Occupied(OccupiedEntry { item, prev, next }) => Entry::Occupied(OccupiedEntry {
        item: clone_item(item),
        prev: *prev,
        next: *next,
      }),
      Entry::Vacant { next_vacant } => Entry::Vacant {
        next_vacant: *next_vacant,
      },
    }));
    VecList {
      entries,
      head: self.head,
      back: self.back,
      vacant_head: self.vacant_head,
      len: self.len,
    }
  }

  /// Get the number of elements in the list.
  pub fn len(&self) -> usize {
    self.len
  }

  /// Check if the list contains an element at a certain ptr. Note that you might suffer from the
  /// ABA problem, that is if you delete an item and add a new item, the pointer to the deleted
  /// item might point to the new item.
  pub fn contains_ptr(&self, ptr: ListPtr) -> bool {
    match &self.entries[ptr.to_usize()] {
      Entry::Occupied(_) => true,
      Entry::Vacant { .. } => false,
    }
  }

  fn get_occupied(&self, ptr: ListPtr) -> &OccupiedEntry<T> {
    let Entry::Occupied(x) = &self.entries[ptr.to_usize()] else {
      panic!("Entry unreachable: {:?}", ptr)
    };
    x
  }

  fn get_occupied_mut(&mut self, ptr: ListPtr) -> &mut OccupiedEntry<T> {
    let Entry::Occupied(x) = &mut self.entries[ptr.to_usize()] else {
      panic!("Entry unreachable: {:?}", ptr)
    };
    x
  }

  /// Get the element pointed to by a pointer. (O(1))
  ///
  /// It is your responsibility that the pointer is valid.
  pub fn get(&self, ptr: ListPtr) -> &T {
    &self.get_occupied(ptr).item
  }

  /// Get a mutable reference to the element pointed to by a pointer. (O(1))
  ///
  /// It is your responsibility that the pointer is valid.
  pub fn get_mut(&mut self, ptr: ListPtr) -> &mut T {
    &mut self.get_occupied_mut(ptr).item
  }

  /// Get a pointer to the head of the list. (O(1))
  pub fn head(&self) -> Option<ListPtr> {
    self.head
  }

  /// Get a pointer to the last elem in the list. (O(1)) (O(1))
  pub fn back(&self) -> Option<ListPtr> {
    self.back
  }

  /// Get the next element in the list. (O(1))
  pub fn next(&self, ptr: ListPtr) -> Option<ListPtr> {
    self.get_occupied(ptr).next
  }

  /// Get the prev element in the list. (O(1))
  pub fn prev(&self, ptr: ListPtr) -> Option<ListPtr> {
    self.get_occupied(ptr).prev
  }

  /// Pop a vacant entry or extend the length of `self.entries` if `self.vacant_head = None`.
  fn take_vacant(&mut self) -> ListPtr {
    if let Some(vacant_head) = self.vacant_head {
      let Entry::Vacant { next_vacant } = self.entries[vacant_head.to_usize()] else {
        panic!("Non vacant entry at vacant_head.");
      };
      self.vacant_head = next_vacant;
      vacant_head
    } else {
      self.entries.push(Entry::Vacant { next_vacant: None });
      ListPtr::from_usize(self.entries.len() - 1)
    }
  }

  /// Insert an element at the head of the list.
  pub fn insert_head(&mut self, item: T) -> ListPtr {
    if let Some(head) = self.head {
      self.insert_before(head, item)
    } else {
      self.len += 1;
      let insert_ptr = self.take_vacant();
      self.entries[insert_ptr.to_usize()] = Entry::Occupied(OccupiedEntry {
        item,
        prev: None,
        next: None,
      });
      self.head = Some(insert_ptr);
      self.back = Some(insert_ptr);
      insert_ptr
    }
  }

  /// Insert an element at the back of the list.
  pub fn insert_back(&mut self, item: T) -> ListPtr {
    if let Some(back) = self.back {
      self.insert_after(back, item)
    } else {
      self.insert_head(item)
    }
  }

  /// Insert an element after this, returning a pointer to the new element. (O(1))
  pub fn insert_after(&mut self, this_ptr: ListPtr, item: T) -> ListPtr {
    self.len += 1;
    let insert_ptr = if let Some(vacant_head) = self.vacant_head {
      let Entry::Vacant { next_vacant } = self.entries[vacant_head.to_usize()] else {
        panic!("Non vacant entry at vacant_head.");
      };
      self.vacant_head = next_vacant;
      vacant_head
    } else {
      self.entries.push(Entry::Vacant { next_vacant: None });
      ListPtr::from_usize(self.entries.len() - 1)
    };
    let this = self.get_occupied_mut(this_ptr);
    let next = this.next;
    this.next = Some(insert_ptr);
    if let Some(next) = next {
      self.get_occupied_mut(next).prev = Some(insert_ptr);
    } else {
      self.back = Some(insert_ptr);
    }
    self.entries[insert_ptr.to_usize()] = Entry::Occupied(OccupiedEntry {
      item,
      prev: Some(this_ptr),
      next,
    });
    insert_ptr
  }

  /// Insert an element before this, returning a pointer to the new element. (O(1))
  pub fn insert_before(&mut self, this_ptr: ListPtr, item: T) -> ListPtr {
    self.len += 1;
    let insert_ptr = if let Some(vacant_head) = self.vacant_head {
      let Entry::Vacant { next_vacant } = self.entries[vacant_head.to_usize()] else {
        panic!("Non vacant entry at vacant_head.");
      };
      self.vacant_head = next_vacant;
      vacant_head
    } else {
      self.entries.push(Entry::Vacant { next_vacant: None });
      ListPtr::from_usize(self.entries.len() - 1)
    };
    let this = self.get_occupied_mut(this_ptr);
    let prev = this.prev;
    this.prev = Some(insert_ptr);
    if let Some(prev) = prev {
      self.get_occupied_mut(prev).next = Some(insert_ptr);
    } else {
      self.head = Some(insert_ptr);
    }
    self.entries[insert_ptr.to_usize()] = Entry::Occupied(OccupiedEntry {
      item,
      next: Some(this_ptr),
      prev,
    });
    insert_ptr
  }

  /// Remove an element.
  pub fn remove(&mut self, remove_ptr: ListPtr) -> T {
    self.len -= 1;
    let Entry::Occupied(removed_entry) =
      mem::replace(&mut self.entries[remove_ptr.to_usize()], Entry::Vacant {
        next_vacant: self.vacant_head,
      })
    else {
      panic!("No occupied entry at remove pointer: {:?}", remove_ptr)
    };
    self.vacant_head = Some(remove_ptr);
    if let Some(next) = removed_entry.next {
      self.get_occupied_mut(next).prev = removed_entry.prev;
    } else {
      self.back = removed_entry.prev;
    }
    if let Some(prev) = removed_entry.prev {
      self.get_occupied_mut(prev).next = removed_entry.next;
    } else {
      self.head = removed_entry.next;
    }
    removed_entry.item
  }

  /// Iterate over all elements in the list.
  pub fn iter(&self) -> impl DoubleEndedIterator<Item = (ListPtr, &T)> + Copy {
    Iter {
      list: self,
      start: self.head,
      end: self.back,
    }
  }
}

#[derive(Debug)]
struct Iter<'a, T, A: Allocator> {
  list: &'a VecList<T, A>,
  start: Option<ListPtr>,
  end: Option<ListPtr>,
}

impl<'a, T, A: Allocator> Iterator for Iter<'a, T, A> {
  type Item = (ListPtr, &'a T);
  fn next(&mut self) -> Option<Self::Item> {
    if let Some(start) = self.start {
      let OccupiedEntry { item, next, .. } = self.list.get_occupied(start);
      self.start = *next;
      if next.is_none() {
        self.end = None;
      }
      Some((start, item))
    } else {
      None
    }
  }
}

impl<'a, T, A: Allocator> DoubleEndedIterator for Iter<'a, T, A> {
  fn next_back(&mut self) -> Option<Self::Item> {
    if let Some(end) = self.end {
      let OccupiedEntry { item, prev, .. } = self.list.get_occupied(end);
      self.end = *prev;
      if prev.is_none() {
        self.start = None;
      }
      Some((end, item))
    } else {
      None
    }
  }
}

impl<'a, T, A: Allocator> Clone for Iter<'a, T, A> {
  fn clone(&self) -> Self {
    Self {
      list: self.list,
      start: self.start,
      end: self.end,
    }
  }
}

impl<'a, T, A: Allocator> Copy for Iter<'a, T, A> {}

impl<T, A: Allocator> Extend<T> for VecList<T, A> {
  fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
    for x in iter {
      self.insert_back(x);
    }
  }
}

impl<T> FromIterator<T> for VecList<T> {
  fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
    let mut list = Self::new();
    for x in iter {
      list.insert_back(x);
    }
    list
  }
}
impl<T: fmt::Debug, A: Allocator> fmt::Debug for VecList<T, A> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "[")?;
    for (ptr, x) in self.iter() {
      write!(f, "{x:?}")?;
      if Some(ptr) != self.back() {
        write!(f, ", ")?;
      }
    }
    write!(f, "]")
  }
}

#[cfg(test)]
mod tests {
  use rand::prelude::*;

  use super::*;

  #[test]
  fn test_vec_list() {
    let mut list: VecList<u64> = VecList::new();
    // A vec with all pointers and values.
    let mut ptr_list: Vec<(ListPtr, u64)> = Vec::new();
    check_lists(&list, &ptr_list);

    // Insert or remove elements. The list will never be longer than 8 items.
    let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(42);
    for _ in 0..1024 {
      // Check if we should remove or insert an element.
      if ptr_list.len() > 0 && (ptr_list.len() >= 8 || rng.gen()) {
        // Remove an element.
        let idx = rng.gen_range(0..ptr_list.len());
        let (ptr, item) = ptr_list.remove(idx);
        let item2 = list.remove(ptr);
        assert_eq!(item, item2);
        assert!(!list.contains_ptr(ptr));
      } else {
        // Insert an element.
        let val = rng.gen();
        // Check if we should insert in the middle or at an end of the list.
        if ptr_list.len() == 0 || rng.gen() {
          // Insert at an end.
          if rng.gen() {
            let ptr = list.insert_head(val);
            ptr_list.insert(0, (ptr, val));
          } else {
            let ptr = list.insert_back(val);
            ptr_list.push((ptr, val));
          }
        } else {
          // Insert in the middle.
          let idx = rng.gen_range(0..=ptr_list.len());
          // Check if we should insert before or after an element.
          let ptr = if idx < ptr_list.len() && (idx == 0 || rng.gen()) {
            list.insert_before(ptr_list[idx].0, val)
          } else {
            list.insert_after(ptr_list[idx - 1].0, val)
          };
          ptr_list.insert(idx, (ptr, val));
        }
      }
      check_lists(&list, &ptr_list);
    }
  }

  fn check_lists(list: &VecList<u64>, ptr_list: &Vec<(ListPtr, u64)>) {
    assert_eq!(list.len(), ptr_list.len());
    // Check forward direction.
    let mut ptr_iter = ptr_list.iter().copied();
    let mut list_iter = list.iter();
    let mut maybe_ptr = list.head();
    loop {
      if let Some((ptr, val)) = ptr_iter.next() {
        assert_eq!(maybe_ptr, Some(ptr));
        assert!(list.contains_ptr(ptr));
        assert_eq!(val, *list.get(ptr),);
        assert_eq!(list_iter.next().unwrap(), (ptr, &val));
        maybe_ptr = list.next(ptr);
      } else {
        assert!(maybe_ptr.is_none());
        assert!(list_iter.next().is_none());
        assert!(list_iter.next_back().is_none());
        break;
      }
    }

    // Check backward direction.
    let mut ptr_iter = ptr_list.iter().copied();
    let mut list_iter = list.iter();
    let mut maybe_ptr = list.back();
    loop {
      if let Some((ptr, val)) = ptr_iter.next_back() {
        assert_eq!(maybe_ptr, Some(ptr));
        assert_eq!(val, *list.get(ptr),);
        assert_eq!(list_iter.next_back().unwrap(), (ptr, &val));
        maybe_ptr = list.prev(ptr);
      } else {
        assert!(maybe_ptr.is_none());
        assert!(list_iter.next().is_none());
        assert!(list_iter.next_back().is_none());
        break;
      }
    }

    // Check the number of vacants.
    let len = ptr_list.len();
    let vacants = list.entries.len() - len;
    let mut maybe_vacant = list.vacant_head;
    for _ in 0..vacants {
      let Some(vacant) = maybe_vacant else {
        unreachable!()
      };
      let Entry::Vacant { next_vacant } = list.entries[vacant.to_usize()] else {
        unreachable!()
      };
      maybe_vacant = next_vacant;
    }
    assert_eq!(maybe_vacant, None);

    // Check clone_map_in().
    let cloned = list.clone_map_in(|x| *x, Global::default());
    assert_eq!(list.entries, cloned.entries);
    assert_eq!(list.head, cloned.head);
    assert_eq!(list.back, cloned.back);
    assert_eq!(list.vacant_head, cloned.vacant_head);
    assert_eq!(list.len, cloned.len);
  }

  #[test]
  fn test_from_iter() {
    let lists = [vec![], vec![1], vec![1, 2], vec![1, 2, 3, 4]];
    for list in lists {
      assert!(
        list
          .iter()
          .collect::<VecList<_>>()
          .iter()
          .map(|(_, x)| *x)
          .eq(list.iter())
      );
    }
  }
}
