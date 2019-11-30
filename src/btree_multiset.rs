// Copyright 2019 multiset developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
#![warn(missing_docs)]

use super::Iter;

use std::borrow::Borrow;
use std::collections::btree_map::{self, Entry, Keys};
use std::collections::BTreeMap;
use std::fmt;
use std::iter::{FromIterator, IntoIterator};
use std::ops::{Add, Sub};

#[derive(Clone)]
/// A tree-based multiset.
pub struct BTreeMultiSet<K> {
    elem_counts: BTreeMap<K, usize>,
    size: usize,
}

impl<K> BTreeMultiSet<K>
where
    K: Ord,
{
    /// Creates a new empty `BTreeMultiSet`.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    ///
    /// let multiset: BTreeMultiSet<char> = BTreeMultiSet::new();
    /// ```
    pub fn new() -> Self {
        BTreeMultiSet {
            elem_counts: BTreeMap::new(),
            size: 0,
        }
    }

    /// An iterator visiting all elements in arbitrary order, including each duplicate.
    /// The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    /// let mut multiset = BTreeMultiSet::new();
    /// multiset.insert(0);
    /// multiset.insert(0);
    /// multiset.insert(1);
    ///
    /// // Will print in an arbitrary order.
    /// for x in multiset.iter() {
    ///     println!("{}", x);
    /// }
    /// assert_eq!(3, multiset.iter().count());
    /// ```
    pub fn iter(&self) -> Iter<&K, &usize, btree_map::Iter<K, usize>> {
        Iter {
            iter: self.elem_counts.iter(),
            duplicate: None,
            duplicate_index: 0,
            _ghost: std::marker::PhantomData,
        }
    }

    /// Returns true if the multiset contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    ///
    /// let mut multiset = BTreeMultiSet::new();
    /// assert!(multiset.is_empty());
    /// multiset.insert(1);
    /// assert!(!multiset.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.elem_counts.is_empty()
    }

    /// Returns `true` if the multiset contains a value.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    ///
    /// let set: BTreeMultiSet<_> = [1, 2, 3].iter().cloned().collect();
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&4), false);
    /// ```
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.elem_counts.contains_key(value)
    }

    /// Counts all the elements, including each duplicate.
    ///
    /// # Examples
    ///
    /// A new empty `BTreeMultiSet` with 0 total elements:
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    ///
    /// let multiset: BTreeMultiSet<char> = BTreeMultiSet::new();
    /// assert_eq!(0, multiset.len());
    /// ```
    ///
    /// A `BTreeMultiSet` from `vec![1,1,2]` has 3 total elements:
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let multiset: BTreeMultiSet<i32> = FromIterator::from_iter(vec![1,1,2]);
    /// assert_eq!(3, multiset.len());
    /// ```
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns all the distinct elements in the `BTreeMultiSet`.
    ///
    /// # Examples
    ///
    /// A `BTreeMultiSet` from `vec![1,1,2]` has 2 distinct elements,
    /// namely `1` and `2`, but not `3`:
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    /// use std::collections::HashSet;
    /// use std::iter::FromIterator;
    ///
    /// let multiset: BTreeMultiSet<i64> = FromIterator::from_iter(vec![1,1,2]);
    /// let distinct = multiset.distinct_elements().collect::<HashSet<_>>();
    /// assert_eq!(2, distinct.len());
    /// assert!(distinct.contains(&1));
    /// assert!(distinct.contains(&2));
    /// assert!(!distinct.contains(&3));
    /// ```
    pub fn distinct_elements<'a>(&'a self) -> Keys<'a, K, usize> {
        self.elem_counts.keys()
    }

    /// Inserts an element.
    ///
    /// # Examples
    ///
    /// Insert `5` into a new `BTreeMultiSet`:
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    ///
    /// let mut multiset: BTreeMultiSet<i32> = BTreeMultiSet::new();
    /// assert_eq!(0, multiset.count_of(&5));
    /// multiset.insert(5);
    /// assert_eq!(1, multiset.count_of(&5));
    /// ```
    pub fn insert(&mut self, val: K) {
        self.insert_times(val, 1);
    }

    /// Inserts an element `n` times.
    ///
    /// # Examples
    ///
    /// Insert three `5`s into a new `BTreeMultiSet`:
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    ///
    /// let mut multiset: BTreeMultiSet<i32> = BTreeMultiSet::new();
    /// assert_eq!(0, multiset.count_of(&5));
    /// multiset.insert_times(5,3);
    /// assert_eq!(3, multiset.count_of(&5));
    /// ```
    pub fn insert_times(&mut self, val: K, n: usize) {
        self.size += n;
        match self.elem_counts.entry(val) {
            Entry::Vacant(view) => {
                view.insert(n);
            }
            Entry::Occupied(mut view) => {
                let v = view.get_mut();
                *v += n;
            }
        }
    }

    /// Remove an element. Removal of a nonexistent element
    /// has no effect.
    ///
    /// # Examples
    ///
    /// Remove `5` from a new `BTreeMultiSet`:
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    ///
    /// let mut multiset: BTreeMultiSet<i32> = BTreeMultiSet::new();
    /// multiset.insert(5);
    /// assert_eq!(1, multiset.count_of(&5));
    /// assert!(multiset.remove(&5));
    /// assert_eq!(0, multiset.count_of(&5));
    /// assert!(!multiset.remove(&5));
    /// ```
    pub fn remove(&mut self, val: &K) -> bool {
        self.remove_times(val, 1) > 0
    }

    /// Remove an element `n` times. If an element is
    /// removed as many or more times than it appears,
    /// it is entirely removed from the multiset.
    ///
    /// # Examples
    ///
    /// Remove `5`s from a `BTreeMultiSet` containing 3 of them.
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    ///
    /// let mut multiset: BTreeMultiSet<i32> = BTreeMultiSet::new();
    /// multiset.insert_times(5, 3);
    /// assert!(multiset.count_of(&5) == 3);
    /// assert!(multiset.remove_times(&5, 2) == 2);
    /// assert!(multiset.len() == 1);
    /// assert!(multiset.count_of(&5) == 1);
    /// assert!(multiset.remove_times(&5, 1) == 1);
    /// assert!(multiset.len() == 0);
    /// assert!(multiset.count_of(&5) == 0);
    /// assert!(multiset.remove_times(&5, 1) == 0);
    /// assert!(multiset.count_of(&5) == 0);
    /// ```
    pub fn remove_times(&mut self, val: &K, times: usize) -> usize {
        {
            let entry = self.elem_counts.get_mut(val);
            if entry.is_some() {
                let count = entry.unwrap();
                if *count > times {
                    *count -= times;
                    self.size -= times;
                    return times;
                }
                self.size -= *count;
            }
        }
        self.elem_counts.remove(val).unwrap_or(0)
    }

    /// Remove all of an element from the multiset.
    ///
    /// # Examples
    ///
    /// Remove all `5`s from a `BTreeMultiSet` containing 3 of them.
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    ///
    /// let mut multiset: BTreeMultiSet<i32> = BTreeMultiSet::new();
    /// multiset.insert_times(5,3);
    /// assert!(multiset.count_of(&5) == 3);
    /// multiset.remove_all(&5);
    /// assert!(multiset.count_of(&5) == 0);
    /// assert!(multiset.len() == 0);
    /// ```
    pub fn remove_all(&mut self, val: &K) {
        self.size -= self.elem_counts.get(val).unwrap_or(&0);
        self.elem_counts.remove(val);
    }

    /// Counts the occurrences of `val`.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    ///
    /// let mut multiset: BTreeMultiSet<u8> = BTreeMultiSet::new();
    /// multiset.insert(0);
    /// multiset.insert(0);
    /// multiset.insert(1);
    /// multiset.insert(0);
    /// assert_eq!(3, multiset.count_of(&0));
    /// assert_eq!(1, multiset.count_of(&1));
    /// ```
    pub fn count_of(&self, val: &K) -> usize {
        self.elem_counts.get(val).map_or(0, |x| *x)
    }
}

impl<T> Add for BTreeMultiSet<T>
where
    T: Ord + Clone,
{
    type Output = BTreeMultiSet<T>;

    /// Combine two `BTreeMultiSet`s by adding the number of each
    /// distinct element.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let lhs: BTreeMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let rhs: BTreeMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// let combined = lhs + rhs;
    /// assert_eq!(3, combined.count_of(&1));
    /// assert_eq!(1, combined.count_of(&2));
    /// assert_eq!(1, combined.count_of(&3));
    /// assert_eq!(1, combined.count_of(&4));
    /// assert_eq!(0, combined.count_of(&5));
    /// ```
    fn add(self, rhs: BTreeMultiSet<T>) -> BTreeMultiSet<T> {
        let mut ret: BTreeMultiSet<T> = BTreeMultiSet::new();
        for val in self.distinct_elements() {
            let count = self.count_of(val);
            ret.insert_times((*val).clone(), count);
        }
        for val in rhs.distinct_elements() {
            let count = rhs.count_of(val);
            ret.insert_times((*val).clone(), count);
        }
        ret
    }
}

impl<T> Sub for BTreeMultiSet<T>
where
    T: Ord + Clone,
{
    type Output = BTreeMultiSet<T>;

    /// Combine two `BTreeMultiSet`s by removing elements
    /// in the second multiset from the first. As with `remove()`
    /// (and set difference), excess elements in the second
    /// multiset are ignored.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let lhs: BTreeMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let rhs: BTreeMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// let combined = lhs - rhs;
    /// assert_eq!(0, combined.count_of(&1));
    /// assert_eq!(1, combined.count_of(&2));
    /// assert_eq!(1, combined.count_of(&3));
    /// assert_eq!(0, combined.count_of(&4));
    /// ```
    fn sub(self, rhs: BTreeMultiSet<T>) -> BTreeMultiSet<T> {
        let mut ret = self.clone();
        for val in rhs.distinct_elements() {
            let count = rhs.count_of(val);
            ret.remove_times(val, count);
        }
        ret
    }
}

impl<A> FromIterator<A> for BTreeMultiSet<A>
where
    A: Ord,
{
    /// Creates a new `BTreeMultiSet` from the elements in an iterable.
    ///
    /// # Examples
    ///
    /// Count occurrences of each `char` in `"hello world"`:
    ///
    /// ```
    /// use multiset::BTreeMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let vals = vec!['h','e','l','l','o',' ','w','o','r','l','d'];
    /// let multiset: BTreeMultiSet<char> = FromIterator::from_iter(vals);
    /// assert_eq!(1, multiset.count_of(&'h'));
    /// assert_eq!(3, multiset.count_of(&'l'));
    /// assert_eq!(0, multiset.count_of(&'z'));
    /// ```
    fn from_iter<T>(iterable: T) -> BTreeMultiSet<A>
    where
        T: IntoIterator<Item = A>,
    {
        let mut multiset: BTreeMultiSet<A> = BTreeMultiSet::new();
        for elem in iterable.into_iter() {
            multiset.insert(elem);
        }
        multiset
    }
}

impl<T> PartialEq for BTreeMultiSet<T>
where
    T: Ord,
{
    fn eq(&self, other: &BTreeMultiSet<T>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.elem_counts
            .iter()
            .all(|(key, count)| other.contains(key) && other.elem_counts.get(key).unwrap() == count)
    }
}

impl<T> Eq for BTreeMultiSet<T> where T: Ord {}

impl<T> fmt::Debug for BTreeMultiSet<T>
where
    T: Ord + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod test_multiset {
    use super::BTreeMultiSet;

    #[test]
    fn test_iterate() {
        let mut a = BTreeMultiSet::new();
        for i in 0..16 {
            a.insert(i);
        }
        for i in 0..8 {
            a.insert(i);
        }
        for i in 0..4 {
            a.insert(i);
        }
        let mut observed: u16 = 0;
        let mut observed_twice: u16 = 0;
        let mut observed_thrice: u16 = 0;
        for k in a.iter() {
            let bit = 1 << *k;
            if observed & bit == 0 {
                observed |= bit;
            } else if observed_twice & bit == 0 {
                observed_twice |= bit;
            } else if observed_thrice & bit == 0 {
                observed_thrice |= bit;
            }
        }
        assert_eq!(observed, 0xFFFF);
        assert_eq!(observed_twice, 0xFF);
        assert_eq!(observed_thrice, 0xF);
    }

    #[test]
    fn test_eq() {
        let mut s1 = BTreeMultiSet::new();
        s1.insert(0);
        s1.insert(1);
        s1.insert(1);
        let mut s2 = BTreeMultiSet::new();
        s2.insert(0);
        s2.insert(1);
        assert!(s1 != s2);
        s2.insert(1);
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_size() {
        let mut set = BTreeMultiSet::new();

        assert_eq!(set.len(), 0);
        set.insert('a');
        assert_eq!(set.len(), 1);
        set.remove(&'a');
        assert_eq!(set.len(), 0);

        set.insert_times('b', 4);
        assert_eq!(set.len(), 4);
        set.insert('b');
        assert_eq!(set.len(), 5);
        set.remove_all(&'b');
        assert_eq!(set.len(), 0);

        set.insert_times('c', 6);
        assert_eq!(set.len(), 6);
        set.insert_times('c', 3);
        assert_eq!(set.len(), 9);
        set.insert('c');
        assert_eq!(set.len(), 10);
        set.insert('d');
        assert_eq!(set.len(), 11);
        set.insert_times('d', 3);
        assert_eq!(set.len(), 14);
        set.remove_all(&'c');
        assert_eq!(set.len(), 4);
        set.remove(&'d');
        assert_eq!(set.len(), 3);
        set.remove_times(&'d', 2);
        assert_eq!(set.len(), 1);
        set.remove(&'d');
        assert_eq!(set.len(), 0);
    }
}
