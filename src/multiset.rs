// Copyright 2019 multiset developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
#![warn(missing_docs)]

use std::borrow::Borrow;
use std::collections::hash_map;
use std::collections::hash_map::{Entry, Keys};
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::iter::{FromIterator, IntoIterator};
use std::ops::{Add, Sub};

/// A hash-based multiset.
#[derive(Clone, Default, Eq)]
pub struct HashMultiSet<K>
where
    K: Eq + Hash,
{
    elem_counts: HashMap<K, usize>,
    size: usize,
}

/// An iterator over the items of a `HashMultiSet`.
///
/// This `struct` is created by the [`iter`] method on [`HashMultiSet`].
#[derive(Clone)]
pub struct Iter<'a, K: 'a> {
    iter: hash_map::Iter<'a, K, usize>,
    duplicate: Option<(&'a K, &'a usize)>,
    duplicate_index: usize,
}

impl<'a, K> Iterator for Iter<'a, K> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        if self.duplicate.is_none() {
            self.duplicate = self.iter.next();
        }
        if let Some((key, count)) = self.duplicate {
            self.duplicate_index += 1;
            if self.duplicate_index >= *count {
                self.duplicate = None;
                self.duplicate_index = 0;
            }
            Some(key)
        } else {
            None
        }
    }
}

impl<K> HashMultiSet<K>
where
    K: Eq + Hash,
{
    /// Creates a new empty `HashMultiSet`.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let multiset: HashMultiSet<char> = HashMultiSet::new();
    /// ```
    pub fn new() -> Self {
        HashMultiSet {
            elem_counts: HashMap::new(),
            size: 0,
        }
    }

    /// An iterator visiting all elements in arbitrary order, including each duplicate.
    /// The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// let mut multiset = HashMultiSet::new();
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
    pub fn iter(&self) -> Iter<K> {
        Iter {
            iter: self.elem_counts.iter(),
            duplicate: None,
            duplicate_index: 0,
        }
    }

    /// Returns true if the multiset contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let mut multiset = HashMultiSet::new();
    /// assert!(multiset.is_empty());
    /// multiset.insert(1);
    /// assert!(!multiset.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.elem_counts.is_empty()
    }

    /// Returns `true` if the multiset contains a value.
    ///
    /// The value may be any borrowed form of the set's value type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let set: HashMultiSet<_> = [1, 2, 3].iter().cloned().collect();
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&4), false);
    /// ```
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.elem_counts.contains_key(value)
    }

    /// Counts all the elements, including each duplicate.
    ///
    /// # Examples
    ///
    /// A new empty `HashMultiSet` with 0 total elements:
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let multiset: HashMultiSet<char> = HashMultiSet::new();
    /// assert_eq!(0, multiset.len());
    /// ```
    ///
    /// A `HashMultiSet` from `vec![1,1,2]` has 3 total elements:
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let multiset: HashMultiSet<i32> = FromIterator::from_iter(vec![1,1,2]);
    /// assert_eq!(3, multiset.len());
    /// ```
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns all the distinct elements in the `HashMultiSet`.
    ///
    /// # Examples
    ///
    /// A `HashMultiSet` from `vec![1,1,2]` has 2 distinct elements,
    /// namely `1` and `2`, but not `3`:
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::collections::HashSet;
    /// use std::iter::FromIterator;
    ///
    /// let multiset: HashMultiSet<i64> = FromIterator::from_iter(vec![1,1,2]);
    /// let distinct = multiset.distinct_elements().collect::<HashSet<_>>();
    /// assert_eq!(2, distinct.len());
    /// assert!(distinct.contains(&1));
    /// assert!(distinct.contains(&2));
    /// assert!(!distinct.contains(&3));
    /// ```
    pub fn distinct_elements(&self) -> Keys<K, usize> {
        self.elem_counts.keys()
    }

    /// Inserts an element.
    ///
    /// # Examples
    ///
    /// Insert `5` into a new `HashMultiSet`:
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let mut multiset: HashMultiSet<i32> = HashMultiSet::new();
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
    /// Insert three `5`s into a new `HashMultiSet`:
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let mut multiset: HashMultiSet<i32> = HashMultiSet::new();
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
    /// Remove `5` from a new `HashMultiSet`:
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let mut multiset: HashMultiSet<i32> = HashMultiSet::new();
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
    /// Remove `5`s from a `HashMultiSet` containing 3 of them.
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let mut multiset: HashMultiSet<i32> = HashMultiSet::new();
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
        if let Some(count) = self.elem_counts.get_mut(val) {
            if *count > times {
                *count -= times;
                self.size -= times;
                return times;
            }
            self.size -= *count;
        }
        self.elem_counts.remove(val).unwrap_or(0)
    }

    /// Remove all of an element from the multiset.
    ///
    /// # Examples
    ///
    /// Remove all `5`s from a `HashMultiSet` containing 3 of them.
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let mut multiset: HashMultiSet<i32> = HashMultiSet::new();
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
    /// use multiset::HashMultiSet;
    ///
    /// let mut multiset: HashMultiSet<u8> = HashMultiSet::new();
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

    /// Returns an iterator over the union of the two sets.
    ///
    /// This entails visiting each key the maximum number of times it appears in either set.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
    /// let set2: HashMultiSet<_> = [2, 2, 3].iter().cloned().collect();
    /// let mut union_vec: Vec<_> = set1.union(&set2).cloned().collect();
    /// union_vec.sort(); // Order is arbitrary
    /// assert_eq!(union_vec, vec![1, 1, 2, 2, 3]);
    /// ```
    pub fn union<'a>(&'a self, other: &'a HashMultiSet<K>) -> Union<'a, K> {
        Union {
            set1_iter: self.elem_counts.iter(),
            set2_iter: other.elem_counts.iter(),
            set1: self,
            set2: other,
            cur_entry: None,
            cur_count: 0,
        }
    }

    /// Returns an iterator over the intersection of the two sets.
    ///
    /// This entails visiting each key the minimum number of times it appears in either set.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let set1: HashMultiSet<_> = [1, 1, 2, 2, 2].iter().cloned().collect();
    /// let set2: HashMultiSet<_> = [1, 2, 2, 3].iter().cloned().collect();
    /// let mut intersection_vec: Vec<_> = set1.intersection(&set2).cloned().collect();
    /// intersection_vec.sort(); // Order is arbitrary
    /// assert_eq!(intersection_vec, vec![1, 2, 2]);
    /// ```
    pub fn intersection<'a>(&'a self, other: &'a HashMultiSet<K>) -> Intersection<'a, K> {
        Intersection {
            set1_iter: self.elem_counts.iter(),
            set2: other,
            cur_entry: None,
            cur_count: 0,
        }
    }

    /// Returns an iterator over the union of the two sets.
    ///
    /// This entails yielding each key with the maximum number of times it appears in either set.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
    /// let set2: HashMultiSet<_> = [2, 2, 3].iter().cloned().collect();
    /// let set_union: HashMultiSet<_> = set1
    ///     .union_counts(&set2)
    ///     .map(|(&key, count)| (key, count))
    ///     .collect();
    /// assert_eq!(set_union.count_of(&1), 2);
    /// assert_eq!(set_union.count_of(&2), 2);
    /// assert_eq!(set_union.count_of(&3), 1);
    /// ```
    pub fn union_counts<'a>(&'a self, other: &'a HashMultiSet<K>) -> UnionCounts<'a, K> {
        UnionCounts {
            set1: self,
            set2: other,
            set1_iter: self.elem_counts.iter(),
            set2_iter: other.elem_counts.iter(),
        }
    }

    /// Return an iterator over the intersection of the two sets.
    ///
    /// This entails yielding each key with the minimum number of times it appears in either set. If
    /// a key only appears in one set, it will not appear at all in the intersection.
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
    /// let set2: HashMultiSet<_> = [2, 2, 3].iter().cloned().collect();
    /// let set_intersection: HashMultiSet<_> = set1
    ///     .intersection_counts(&set2)
    ///     .map(|(&key, count)| (key, count))
    ///     .collect();
    /// assert_eq!(set_intersection.count_of(&1), 0);
    /// assert_eq!(set_intersection.count_of(&2), 1);
    /// assert_eq!(set_intersection.count_of(&3), 0);
    /// ```
    pub fn intersection_counts<'a>(
        &'a self,
        other: &'a HashMultiSet<K>,
    ) -> IntersectionCounts<'a, K> {
        IntersectionCounts {
            set2: other,
            set1_iter: self.elem_counts.iter(),
        }
    }
}

/// An iterator over the union of two structs. See [HashMultiSet::union] for
/// more details.
pub struct Union<'a, K> {
    set1_iter: hash_map::Iter<'a, K, usize>,
    set2_iter: hash_map::Iter<'a, K, usize>,
    set1: &'a HashMultiSet<K>,
    set2: &'a HashMultiSet<K>,
    cur_entry: Option<(&'a K, usize)>,
    cur_count: usize,
}

impl<'a, K> Iterator for Union<'a, K>
where
    K: Eq + Hash,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((key, count)) = self.cur_entry {
            if self.cur_count < count {
                self.cur_count += 1;
                return Some(key);
            }
        }
        if let Some((new_key, &new_count)) = self.set1_iter.next() {
            let max_count = std::cmp::max(new_count, self.set2.count_of(new_key));
            self.cur_entry = Some((new_key, max_count));
            self.cur_count = 0;
            return self.next();
        }
        while let Some((new_key, &new_count)) = self.set2_iter.next() {
            if self.set1.contains(new_key) {
                continue;
            }
            self.cur_entry = Some((new_key, new_count));
            self.cur_count = 0;
            return self.next();
        }
        None
    }
}

/// An iterator over the intersection of two structs. See
/// [HashMultiSet::intersection] for more details.
pub struct Intersection<'a, K> {
    set1_iter: hash_map::Iter<'a, K, usize>,
    set2: &'a HashMultiSet<K>,
    cur_entry: Option<(&'a K, usize)>,
    cur_count: usize,
}

impl<'a, K> Iterator for Intersection<'a, K>
where
    K: Eq + Hash,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((key, count)) = self.cur_entry {
            if self.cur_count < count {
                self.cur_count += 1;
                return Some(key);
            }
        }
        if let Some((new_key, &new_count)) = self.set1_iter.next() {
            let min_count = std::cmp::min(new_count, self.set2.count_of(new_key));
            self.cur_entry = Some((new_key, min_count));
            self.cur_count = 0;
            return self.next();
        }
        None
    }
}

/// An iterator over the union of two structs. See [HashMultiSet::union] for
/// more details.
pub struct UnionCounts<'a, K> {
    set1: &'a HashMultiSet<K>,
    set2: &'a HashMultiSet<K>,
    set1_iter: hash_map::Iter<'a, K, usize>,
    set2_iter: hash_map::Iter<'a, K, usize>,
}

impl<'a, K> Iterator for UnionCounts<'a, K>
where
    K: Eq + Hash,
{
    type Item = (&'a K, usize);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key, count)) = self.set1_iter.next() {
            let max_count = std::cmp::max(*count, self.set2.count_of(key));
            return Some((key, max_count));
        }
        while let Some((key, count)) = self.set2_iter.next() {
            if !self.set1.contains(key) {
                return Some((key, *count));
            }
        }
        None
    }
}

/// An iterator over the intersection of two structs. See
/// [HashMultiSet::intersection] for more details.
pub struct IntersectionCounts<'a, K> {
    set2: &'a HashMultiSet<K>,
    set1_iter: hash_map::Iter<'a, K, usize>,
}

impl<'a, K> Iterator for IntersectionCounts<'a, K>
where
    K: Eq + Hash,
{
    type Item = (&'a K, usize);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key, count)) = self.set1_iter.next() {
            if self.set2.contains(key) {
                let min_count = std::cmp::min(*count, self.set2.count_of(key));
                return Some((key, min_count));
            }
        }
        None
    }
}

impl<T> Add for HashMultiSet<T>
where
    T: Eq + Hash + Clone,
{
    type Output = HashMultiSet<T>;

    /// Combine two `HashMultiSet`s by adding the number of each
    /// distinct element.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let lhs: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let rhs: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// let combined = lhs + rhs;
    /// assert_eq!(3, combined.count_of(&1));
    /// assert_eq!(1, combined.count_of(&2));
    /// assert_eq!(1, combined.count_of(&3));
    /// assert_eq!(1, combined.count_of(&4));
    /// assert_eq!(0, combined.count_of(&5));
    /// ```
    fn add(mut self, rhs: HashMultiSet<T>) -> HashMultiSet<T> {
        for (val, count) in rhs.elem_counts {
            self.insert_times(val, count);
        }
        self
    }
}

impl<T> Sub for HashMultiSet<T>
where
    T: Eq + Hash + Clone,
{
    type Output = HashMultiSet<T>;

    /// Combine two `HashMultiSet`s by removing elements
    /// in the second multiset from the first. As with `remove()`
    /// (and set difference), excess elements in the second
    /// multiset are ignored.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let lhs: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let rhs: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// let combined = lhs - rhs;
    /// assert_eq!(0, combined.count_of(&1));
    /// assert_eq!(1, combined.count_of(&2));
    /// assert_eq!(1, combined.count_of(&3));
    /// assert_eq!(0, combined.count_of(&4));
    /// ```
    fn sub(mut self, rhs: HashMultiSet<T>) -> HashMultiSet<T> {
        for (val, count) in rhs.elem_counts {
            self.remove_times(&val, count);
        }
        self
    }
}

impl<A> FromIterator<A> for HashMultiSet<A>
where
    A: Eq + Hash,
{
    /// Creates a new `HashMultiSet` from the elements in an iterable.
    ///
    /// # Examples
    ///
    /// Count occurrences of each `char` in `"hello world"`:
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let vals = vec!['h','e','l','l','o',' ','w','o','r','l','d'];
    /// let multiset: HashMultiSet<char> = FromIterator::from_iter(vals);
    /// assert_eq!(1, multiset.count_of(&'h'));
    /// assert_eq!(3, multiset.count_of(&'l'));
    /// assert_eq!(0, multiset.count_of(&'z'));
    /// ```
    fn from_iter<T>(iterable: T) -> HashMultiSet<A>
    where
        T: IntoIterator<Item = A>,
    {
        let mut multiset: HashMultiSet<A> = HashMultiSet::new();
        for elem in iterable {
            multiset.insert(elem);
        }
        multiset
    }
}

impl<K> FromIterator<(K, usize)> for HashMultiSet<K>
where
    K: Eq + Hash,
{
    /// Creates a new `HashMultiSet` from the elements in an iterable.
    ///
    /// # Examples
    ///
    /// Count occurrences of each `char` in `"hello world"`:
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let vals = vec!['h','e','l','l','o',' ','w','o','r','l','d'];
    /// let multiset: HashMultiSet<char> = FromIterator::from_iter(vals);
    /// assert_eq!(1, multiset.count_of(&'h'));
    /// assert_eq!(3, multiset.count_of(&'l'));
    /// assert_eq!(0, multiset.count_of(&'z'));
    /// ```
    fn from_iter<T>(iterable: T) -> HashMultiSet<K>
    where
        T: IntoIterator<Item = (K, usize)>,
    {
        let mut multiset: HashMultiSet<K> = HashMultiSet::new();
        for (elem, count) in iterable.into_iter() {
            multiset.insert_times(elem, count);
        }
        multiset
    }
}

impl<T> PartialEq for HashMultiSet<T>
where
    T: Eq + Hash,
{
    fn eq(&self, other: &HashMultiSet<T>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.elem_counts
            .iter()
            .all(|(key, count)| other.contains(key) && other.elem_counts.get(key).unwrap() == count)
    }
}

impl<T> fmt::Debug for HashMultiSet<T>
where
    T: Eq + Hash + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod test_multiset {
    use super::HashMultiSet;

    #[test]
    fn test_iterate() {
        let mut a = HashMultiSet::new();
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
        let mut s1 = HashMultiSet::new();
        s1.insert(0);
        s1.insert(1);
        s1.insert(1);
        let mut s2 = HashMultiSet::new();
        s2.insert(0);
        s2.insert(1);
        assert!(s1 != s2);
        s2.insert(1);
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_size() {
        let mut set = HashMultiSet::new();

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

        set.insert_times('e', 2);
        assert_eq!(set.len(), 2);
        assert_eq!(set.remove_times(&'e', 4), 2);
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_union() {
        let empty_array: [u32; 0] = [];

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [2, 2, 3].iter().cloned().collect();
        let mut union_vec: Vec<_> = set1.union(&set2).cloned().collect();
        union_vec.sort();
        assert_eq!(union_vec, vec![1, 1, 2, 2, 3]);

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [3, 4, 4].iter().cloned().collect();
        let mut union_vec: Vec<_> = set1.union(&set2).cloned().collect();
        union_vec.sort();
        assert_eq!(union_vec, vec![1, 1, 2, 3, 4, 4]);

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let mut union_vec: Vec<_> = set1.union(&set2).cloned().collect();
        union_vec.sort();
        assert_eq!(union_vec, vec![1, 1, 2]);

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1, 2, 2].iter().cloned().collect();
        let mut union_vec: Vec<_> = set1.union(&set2).cloned().collect();
        union_vec.sort();
        assert_eq!(union_vec, vec![1, 1, 2, 2]);

        let set1: HashMultiSet<_> = [1, 1, 2, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let mut union_vec: Vec<_> = set1.union(&set2).cloned().collect();
        union_vec.sort();
        assert_eq!(union_vec, vec![1, 1, 2, 2]);

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 2, 2].iter().cloned().collect();
        let mut union_vec: Vec<_> = set1.union(&set2).cloned().collect();
        union_vec.sort();
        assert_eq!(union_vec, vec![1, 1, 2, 2]);

        let set1: HashMultiSet<_> = empty_array.iter().cloned().collect();
        let set2: HashMultiSet<_> = [2, 2, 3].iter().cloned().collect();
        let mut union_vec: Vec<_> = set1.union(&set2).cloned().collect();
        union_vec.sort();
        assert_eq!(union_vec, vec![2, 2, 3]);

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = empty_array.iter().cloned().collect();
        let mut union_vec: Vec<_> = set1.union(&set2).cloned().collect();
        union_vec.sort();
        assert_eq!(union_vec, vec![1, 1, 2]);

        let set1: HashMultiSet<_> = empty_array.iter().cloned().collect();
        let set2: HashMultiSet<_> = empty_array.iter().cloned().collect();
        let mut union_vec: Vec<_> = set1.union(&set2).cloned().collect();
        union_vec.sort();
        assert_eq!(union_vec, vec![]);
    }

    #[test]
    fn test_intersection() {
        let empty_array: [u32; 0] = [];

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [2, 2, 3].iter().cloned().collect();
        let mut intersection_vec: Vec<_> = set1.intersection(&set2).cloned().collect();
        intersection_vec.sort();
        assert_eq!(intersection_vec, vec![2]);

        let set1: HashMultiSet<_> = [1, 1, 2, 2, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 2, 2, 3].iter().cloned().collect();
        let mut intersection_vec: Vec<_> = set1.intersection(&set2).cloned().collect();
        intersection_vec.sort();
        assert_eq!(intersection_vec, vec![1, 2, 2]);

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [3, 4, 4].iter().cloned().collect();
        let mut intersection_vec: Vec<_> = set1.intersection(&set2).cloned().collect();
        intersection_vec.sort();
        assert_eq!(intersection_vec, vec![]);

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let mut intersection_vec: Vec<_> = set1.intersection(&set2).cloned().collect();
        intersection_vec.sort();
        assert_eq!(intersection_vec, vec![1, 1, 2]);

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1, 2, 2].iter().cloned().collect();
        let mut intersection_vec: Vec<_> = set1.intersection(&set2).cloned().collect();
        intersection_vec.sort();
        assert_eq!(intersection_vec, vec![1, 1, 2]);

        let set1: HashMultiSet<_> = [1, 1, 2, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let mut intersection_vec: Vec<_> = set1.intersection(&set2).cloned().collect();
        intersection_vec.sort();
        assert_eq!(intersection_vec, vec![1, 1, 2]);

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 2, 2].iter().cloned().collect();
        let mut intersection_vec: Vec<_> = set1.intersection(&set2).cloned().collect();
        intersection_vec.sort();
        assert_eq!(intersection_vec, vec![1, 2]);

        let set1: HashMultiSet<_> = empty_array.iter().cloned().collect();
        let set2: HashMultiSet<_> = [2, 2, 3].iter().cloned().collect();
        let mut intersection_vec: Vec<_> = set1.intersection(&set2).cloned().collect();
        intersection_vec.sort();
        assert_eq!(intersection_vec, vec![]);

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = empty_array.iter().cloned().collect();
        let mut intersection_vec: Vec<_> = set1.intersection(&set2).cloned().collect();
        intersection_vec.sort();
        assert_eq!(intersection_vec, vec![]);

        let set1: HashMultiSet<_> = empty_array.iter().cloned().collect();
        let set2: HashMultiSet<_> = empty_array.iter().cloned().collect();
        let mut intersection_vec: Vec<_> = set1.intersection(&set2).cloned().collect();
        intersection_vec.sort();
        assert_eq!(intersection_vec, vec![]);
    }

    #[test]
    fn test_union_counts() {
        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [2, 2, 3].iter().cloned().collect();
        let set_union: HashMultiSet<_> = set1
            .union_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_union.count_of(&1), 2);
        assert_eq!(set_union.count_of(&2), 2);
        assert_eq!(set_union.count_of(&3), 1);

        let set1: HashMultiSet<_> = [1, 1].iter().cloned().collect();
        let set2: HashMultiSet<_> = [2, 3].iter().cloned().collect();
        let set_union: HashMultiSet<_> = set1
            .union_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_union.count_of(&1), 2);
        assert_eq!(set_union.count_of(&2), 1);
        assert_eq!(set_union.count_of(&3), 1);
        assert_eq!(set_union.len(), 4);

        let set1: HashMultiSet<_> = [1, 1].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1].iter().cloned().collect();
        let set_union: HashMultiSet<_> = set1
            .union_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_union.count_of(&1), 2);
        assert_eq!(set_union.len(), 2);

        let set1: HashMultiSet<_> = [1, 1].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1, 1].iter().cloned().collect();
        let set_union: HashMultiSet<_> = set1
            .union_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_union.count_of(&1), 3);
        assert_eq!(set_union.len(), 3);

        let set1: HashMultiSet<_> = [1, 1].iter().cloned().collect();
        let set2: HashMultiSet<_> = [2, 2, 2].iter().cloned().collect();
        let set_union: HashMultiSet<_> = set1
            .union_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_union.count_of(&1), 2);
        assert_eq!(set_union.count_of(&2), 3);
        assert_eq!(set_union.len(), 5);

        let set1: HashMultiSet<_> = [1, 1, 2, 3].iter().cloned().collect();
        let empty_array: [u32; 0] = [];
        let set2: HashMultiSet<_> = empty_array.iter().cloned().collect();
        let set_union: HashMultiSet<_> = set1
            .union_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_union.count_of(&1), 2);
        assert_eq!(set_union.count_of(&2), 1);
        assert_eq!(set_union.count_of(&3), 1);
        assert_eq!(set_union.len(), 4);

        let set1: HashMultiSet<_> = [1, 1, 2, 3].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1, 2, 3].iter().cloned().collect();
        let set_union: HashMultiSet<_> = set1
            .union_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_union.count_of(&1), 2);
        assert_eq!(set_union.count_of(&2), 1);
        assert_eq!(set_union.count_of(&3), 1);
        assert_eq!(set_union.len(), 4);
    }

    #[test]
    fn test_intersection_counts() {
        let set1: HashMultiSet<_> = [1, 1].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1, 1].iter().cloned().collect();
        let set_intersection: HashMultiSet<_> = set1
            .intersection_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_intersection.count_of(&1), 2);
        assert_eq!(set_intersection.len(), 2);

        let set1: HashMultiSet<_> = [1, 1].iter().cloned().collect();
        let set2: HashMultiSet<_> = [2, 2, 2].iter().cloned().collect();
        let set_intersection: HashMultiSet<_> = set1
            .intersection_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_intersection.count_of(&1), 0);
        assert_eq!(set_intersection.count_of(&2), 0);
        assert_eq!(set_intersection.len(), 0);

        let set1: HashMultiSet<_> = [1, 1, 2].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1, 3].iter().cloned().collect();
        let set_intersection: HashMultiSet<_> = set1
            .intersection_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_intersection.count_of(&1), 2);
        assert_eq!(set_intersection.count_of(&2), 0);
        assert_eq!(set_intersection.count_of(&3), 0);
        assert_eq!(set_intersection.len(), 2);

        let set1: HashMultiSet<_> = [1, 1, 2, 3].iter().cloned().collect();
        let empty_array: [u32; 0] = [];
        let set2: HashMultiSet<_> = empty_array.iter().cloned().collect();
        let set_intersection: HashMultiSet<_> = set1
            .intersection_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_intersection.count_of(&1), 0);
        assert_eq!(set_intersection.count_of(&2), 0);
        assert_eq!(set_intersection.count_of(&3), 0);
        assert_eq!(set_intersection.len(), 0);

        let set1: HashMultiSet<_> = [1, 1, 2, 3].iter().cloned().collect();
        let set2: HashMultiSet<_> = [1, 1, 2, 3].iter().cloned().collect();
        let set_intersection: HashMultiSet<_> = set1
            .intersection_counts(&set2)
            .map(|(&key, count)| (key, count))
            .collect();
        assert_eq!(set_intersection.count_of(&1), 2);
        assert_eq!(set_intersection.count_of(&2), 1);
        assert_eq!(set_intersection.count_of(&3), 1);
        assert_eq!(set_intersection.len(), 4);
    }
}
