//! An implementation of a doubly linked list where all items are stored in a `Vec`.

use std::mem;

use nonmax::NonMaxUsize;

/// A pointer to an element in a list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
#[derive(Debug, Clone)]
struct OccupiedEntry<T> {
  item: T,
  prev: Option<ListPtr>,
  next: Option<ListPtr>,
}

/// An entry in a list.
#[derive(Debug, Clone)]
enum Entry<T> {
  Occupied(OccupiedEntry<T>),
  Vacant {
    /// The next vacant entry.
    next_vacant: Option<ListPtr>,
  },
}

#[derive(Debug, Clone)]
pub struct VecList<T> {
  entries: Vec<Entry<T>>,
  head: Option<ListPtr>,
  back: Option<ListPtr>,
  vacant_head: Option<ListPtr>,
}

impl<T> VecList<T> {
  /// Create a new empty list.
  pub fn new() -> Self {
    Self {
      entries: Vec::new(),
      head: None,
      back: None,
      vacant_head: None,
    }
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
    let Entry::Occupied(removed_entry) = mem::replace(
      &mut self.entries[remove_ptr.to_usize()],
      Entry::Vacant {
        next_vacant: self.vacant_head,
      },
    ) else {
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
struct Iter<'a, T> {
  list: &'a VecList<T>,
  start: Option<ListPtr>,
  end: Option<ListPtr>,
}

impl<'a, T> Iterator for Iter<'a, T> {
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

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
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

impl<'a, T> Clone for Iter<'a, T> {
  fn clone(&self) -> Self {
    Self {
      list: self.list,
      start: self.start,
      end: self.end,
    }
  }
}

impl<'a, T> Copy for Iter<'a, T> {}

impl<T> FromIterator<T> for VecList<T> {
  fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
    let mut list = VecList::new();
    for x in iter {
      list.insert_back(x);
    }
    list
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
