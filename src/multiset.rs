#![warn(missing_docs)]

use std::collections::{HashMap};
use std::collections::hash_map::{Entry,Keys};
use std::hash::{Hash};
use std::iter::{FromIterator,IntoIterator};
use std::ops::{Add, AddAssign, Sub, SubAssign};

/// A hash-based multiset.
#[derive(Clone)]
pub struct HashMultiSet<K>
{
    elem_counts: HashMap<K, usize>
}

impl<K> HashMultiSet<K> where
    K: Eq + Hash
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
        HashMultiSet { elem_counts: HashMap::new() }
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
    /// assert_eq!(0, multiset.total_elements());
    /// ```
    ///
    /// A `HashMultiSet` from `vec![1,1,2]` has 3 total elements:
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let multiset: HashMultiSet<i32> = FromIterator::from_iter(vec![1,1,2]);
    /// assert_eq!(3, multiset.total_elements());
    /// ```
    pub fn total_elements(&self) -> usize {
        self.elem_counts
            .values()
            .fold(0, |a,b| a + *b)
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
    pub fn distinct_elements<'a>(&'a self) -> Keys<'a, K, usize> {
        self.elem_counts
            .keys()
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
    /// assert_eq!(0, multiset.count_of(5));
    /// multiset.insert(5);
    /// assert_eq!(1, multiset.count_of(5));
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
    /// assert_eq!(0, multiset.count_of(5));
    /// multiset.insert_times(5,3);
    /// assert_eq!(3, multiset.count_of(5));
    /// ```
    pub fn insert_times(&mut self, val: K, n: usize) {
        match self.elem_counts.entry(val) {
            Entry::Vacant(view) => {
                view.insert(n);
            },
            Entry::Occupied(mut view) => {
                let v = view.get_mut();
                *v += n;
            },
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
    /// assert_eq!(1, multiset.count_of(5));
    /// multiset.remove(5);
    /// assert_eq!(0, multiset.count_of(5));
    /// ```
    pub fn remove(&mut self, val: K) {
        self.remove_times(val, 1);
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
    /// multiset.insert_times(5,3);
    /// assert!(multiset.count_of(5) == 3);
    /// multiset.remove_times(5,2);
    /// assert!(multiset.count_of(5) == 1);
    /// multiset.remove_times(5,1);
    /// assert!(multiset.count_of(5) == 0);
    /// multiset.remove_times(5,1);
    /// assert!(multiset.count_of(5) == 0);
    /// ```
    pub fn remove_times(&mut self, val: K, n: usize) {
        match self.elem_counts.entry(val) {
            Entry::Vacant(_) => (),
            Entry::Occupied(mut view) => {
                let v = *view.get();
                if v > n {
                    let v = view.get_mut();
                    *v -= n
                } else {
                    let _ = view.remove_entry();
                };
            },
        }
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
    /// assert!(multiset.count_of(5) == 3);
    /// multiset.remove_all(5);
    /// assert!(multiset.count_of(5) == 0);
    /// ```
    pub fn remove_all(&mut self, val: K) {
        match self.elem_counts.entry(val) {
            Entry::Vacant(_) => (),
            Entry::Occupied(view) => {
                let _ = view.remove_entry();
            },
        }
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
    /// assert_eq!(3, multiset.count_of(0));
    /// assert_eq!(1, multiset.count_of(1));
    /// ```
    pub fn count_of(&self, val: K) -> usize {
        self.elem_counts
            .get(&val)
            .map_or(0, |x| *x)
    }
}

impl<T> Add for HashMultiSet<T> where
    T: Eq + Hash + Clone
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
    /// assert_eq!(3, combined.count_of(1));
    /// assert_eq!(1, combined.count_of(2));
    /// assert_eq!(1, combined.count_of(3));
    /// assert_eq!(1, combined.count_of(4));
    /// assert_eq!(0, combined.count_of(5));
    /// ```
    fn add(self, rhs: HashMultiSet<T>) ->  HashMultiSet<T> {
        let mut ret: HashMultiSet<T> = HashMultiSet::new();
        for val in self.distinct_elements() {
            let count = self.count_of((*val).clone());
            ret.insert_times((*val).clone(), count);
        }
        for val in rhs.distinct_elements() {
            let count = rhs.count_of((*val).clone());
            ret.insert_times((*val).clone(), count);
        }
        ret
    }
}

impl<T> AddAssign for HashMultiSet<T> where
    T: Eq + Hash + Clone
{
    /// Insert the elements of one `HashMultiSet` into another.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let mut lhs: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let rhs: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// lhs += rhs;
    /// assert_eq!(3, lhs.count_of(1));
    /// assert_eq!(1, lhs.count_of(2));
    /// assert_eq!(1, lhs.count_of(3));
    /// assert_eq!(1, lhs.count_of(4));
    /// assert_eq!(0, lhs.count_of(5));
    /// ```
    fn add_assign(&mut self, rhs: HashMultiSet<T>) {
        for val in rhs.distinct_elements() {
            let count = rhs.count_of((*val).clone());
            self.insert_times((*val).clone(), count);
        }
    }
}

impl<T> Sub for HashMultiSet<T> where
    T: Eq + Hash + Clone
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
    /// assert_eq!(0, combined.count_of(1));
    /// assert_eq!(1, combined.count_of(2));
    /// assert_eq!(1, combined.count_of(3));
    /// assert_eq!(0, combined.count_of(4));
    /// ```
    fn sub(self, rhs: HashMultiSet<T>) ->  HashMultiSet<T> {
        let mut ret = self.clone();
        for val in rhs.distinct_elements() {
            let count = rhs.count_of((*val).clone());
            ret.remove_times((*val).clone(), count);
        }
        ret
    }
}

impl<T> SubAssign for HashMultiSet<T> where
    T: Eq + Hash + Clone
{
    /// Remove the elements of one `HashMultiSet` from another
    /// using `-`.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let mut lhs: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let rhs: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// lhs -= rhs;
    /// assert_eq!(0, lhs.count_of(1));
    /// assert_eq!(1, lhs.count_of(2));
    /// assert_eq!(1, lhs.count_of(3));
    /// assert_eq!(0, lhs.count_of(4));
    /// ```
    fn sub_assign(&mut self, rhs: HashMultiSet<T>) {
        for val in rhs.distinct_elements() {
            let count = rhs.count_of((*val).clone());
            self.remove_times((*val).clone(), count);
        }
    }
}

impl<A> FromIterator<A> for HashMultiSet<A> where
    A: Eq + Hash
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
    /// assert_eq!(1, multiset.count_of('h'));
    /// assert_eq!(3, multiset.count_of('l'));
    /// assert_eq!(0, multiset.count_of('z'));
    /// ```
    fn from_iter<T>(iterable: T) -> HashMultiSet<A> where
        T: IntoIterator<Item=A>
    {
        let mut multiset: HashMultiSet<A> = HashMultiSet::new();
        for elem in iterable.into_iter() {
            multiset.insert(elem);
        }
        multiset
    }
}
