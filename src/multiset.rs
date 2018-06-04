#![warn(missing_docs)]

use std::collections::{HashMap};
use std::collections::hash_map::{Entry,Keys};
use std::hash::{Hash};
use std::iter::{FromIterator,IntoIterator};
use std::ops::{Add, AddAssign, Sub, SubAssign};
use std::cmp::Ordering;

/// A hash-based multiset.
#[derive(Clone)]
pub struct HashMultiSet<K>
{
    elem_counts: HashMap<K, usize>
}

/// Test the degree to which the RHS is contained by the LHS.
/// * A result of `Equal` means that the LHS exactly
/// matches on all RHS elements.
/// * A result of `Greater` means that the LHS contains
/// all present RHS elements and overcontains at least one.
/// * A result of `Less` means only that the containment
/// does not hold.
fn containment<T>(lhs: &HashMultiSet<T>,
                  rhs: &HashMultiSet<T>) -> Ordering
    where T: Eq + Hash
{
    let mut result = Ordering::Equal;
    for val in rhs.distinct_elements() {
        let nlhs = match lhs.elem_counts.get(&val) {
            None => 0,
            Some(np) => *np
        };
        if nlhs == 0 {
            return Ordering::Less;
        };
        let nrhs = *rhs.elem_counts.get(&val).unwrap();
        if nrhs > nlhs {
            return Ordering::Less;
        } else if nrhs < nlhs {
            result = Ordering::Greater;
        };
    };
    result
}

#[test]
fn test_containment() {
    let s1: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    let s2: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    let s3: HashMultiSet<isize> = FromIterator::from_iter(vec![2,3]);
    let s4: HashMultiSet<isize> = FromIterator::from_iter(vec![1,4]);
    assert_eq!(Ordering::Equal, containment(&s1, &s1));
    assert_eq!(Ordering::Less, containment(&s1, &s2));
    assert_eq!(Ordering::Less, containment(&s2, &s1));
    assert_eq!(Ordering::Equal, containment(&s1, &s3));
    assert_eq!(Ordering::Less, containment(&s3, &s1));
    assert_eq!(Ordering::Greater, containment(&s2, &s4));
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
    /// MultiSets are partial-ordered by containment: if
    /// they are equal, they are `Equal`; if one is a proper
    /// subset of the other they are `Less` or `Greater`;
    /// otherwise they are unordered. This function is
    /// useful in implementing `PartialOrd` as containment
    /// ordering if desired.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    /// use std::cmp::Ordering;
    ///
    /// let s1: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let s2: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// let s3: HashMultiSet<isize> = FromIterator::from_iter(vec![2,3]);
    /// let s4: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,2,3]);
    /// assert_eq!(None, s1.partial_cmp(&s2));
    /// assert_eq!(Some(Ordering::Less), s3.partial_cmp(&s1));    
    /// assert_eq!(Some(Ordering::Less), s1.partial_cmp(&s4));
    /// assert_eq!(Some(Ordering::Greater), s1.partial_cmp(&s3));
    /// assert_eq!(Some(Ordering::Equal), s1.partial_cmp(&s1));
    /// assert_eq!(Some(Ordering::Greater), s4.partial_cmp(&s1));
    /// ```
    pub fn partial_cmp(&self, other: &HashMultiSet<K>) -> Option<Ordering> {
        match containment(self, other) {
            Ordering::Less => {
                match containment(other, self) {
                    Ordering::Less => None,
                    _ => Some(Ordering::Less)
                }
            },
            Ordering::Equal => {
                match containment(other, self) {
                    Ordering::Less => Some(Ordering::Greater),
                    Ordering::Equal => Some(Ordering::Equal),
                    Ordering::Greater => panic!("=> ordering observed")
                }
            },
            Ordering::Greater => Some(Ordering::Greater)
        }
    }

    /// The given multiset properly contains this one.  This
    /// is computed more efficiently than with
    /// `partial_cmp()` in some cases.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let s1: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let s2: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// let s3: HashMultiSet<isize> = FromIterator::from_iter(vec![2,3]);
    /// assert!(s1.is_submultiset(&s1));
    /// assert!(s3.is_submultiset(&s1));
    /// assert!(!s1.is_submultiset(&s2));
    /// assert!(!s2.is_submultiset(&s1));
    /// assert!(!s1.is_submultiset(&s3));
    /// ```
    pub fn is_submultiset(&self, other: &HashMultiSet<K>) -> bool {
        containment(other, self) != Ordering::Less
    }

    /// The given multiset properly contains this one.
    /// That is, every element of this multiset is
    /// is in the given multiset, plus at least one more.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let s1: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let s2: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// let s3: HashMultiSet<isize> = FromIterator::from_iter(vec![2,3]);
    /// assert!(s3.is_proper_submultiset(&s1));
    /// assert!(!s1.is_proper_submultiset(&s1));
    /// assert!(!s1.is_proper_submultiset(&s2));
    /// assert!(!s2.is_proper_submultiset(&s1));
    /// assert!(!s1.is_proper_submultiset(&s3));
    /// ```
    pub fn is_proper_submultiset(&self, other: &HashMultiSet<K>) -> bool {
        self.partial_cmp(other) == Some(Ordering::Less)
    }
}

impl<T> AsRef<HashMultiSet<T>> for HashMultiSet<T> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<T, U> Add<U> for HashMultiSet<T> where
    T: Eq + Hash + Clone,
    U: AsRef<HashMultiSet<T>>
{
    type Output = HashMultiSet<T>;
    fn add(self, rhs: U) ->  HashMultiSet<T> {
        &self + rhs.as_ref()
    }
}

impl<'a, T, U> Add<U> for &'a HashMultiSet<T> where
    T: Eq + Hash + Clone,
    U: AsRef<HashMultiSet<T>>
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
    fn add(self, rhs: U) ->  HashMultiSet<T> {
        let rhs = rhs.as_ref();
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

impl<T, U> AddAssign<U> for HashMultiSet<T> where
    T: Eq + Hash + Clone,
    U: AsRef<HashMultiSet<T>>
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
    fn add_assign(&mut self, rhs: U) {
        let rhs = rhs.as_ref();
        for val in rhs.distinct_elements() {
            let count = rhs.count_of((*val).clone());
            self.insert_times((*val).clone(), count);
        }
    }
}

impl<T, U> Sub<U> for HashMultiSet<T> where
    T: Eq + Hash + Clone,
    U: AsRef<HashMultiSet<T>>
{
    type Output = HashMultiSet<T>;
    fn sub(self, rhs: U) ->  HashMultiSet<T> {
        &self - rhs.as_ref()
    }
}

impl<'a, T, U> Sub<U> for &'a HashMultiSet<T> where
    T: Eq + Hash + Clone,
    U: AsRef<HashMultiSet<T>>
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
    fn sub(self, rhs: U) ->  HashMultiSet<T> {
        let rhs = rhs.as_ref();
        let mut ret = self.clone();
        for val in rhs.distinct_elements() {
            let count = rhs.count_of((*val).clone());
            ret.remove_times((*val).clone(), count);
        }
        ret
    }
}

impl<T, U> SubAssign<U> for HashMultiSet<T> where
    T: Eq + Hash + Clone,
    U: AsRef<HashMultiSet<T>>
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
    fn sub_assign(&mut self, rhs: U) {
        let rhs = rhs.as_ref();
        for val in rhs.distinct_elements() {
            let count = rhs.count_of((*val).clone());
            self.remove_times((*val).clone(), count);
        }
    }
}


impl<T> PartialEq for HashMultiSet<T> where
    T: Eq + Hash + Clone
{
    /// The obvious definition of equality: exactly the
    /// same number of the same elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let s1: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let s2: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// let s3: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2]);
    /// assert!(s1 == s1);
    /// assert!(s1 != s2);
    /// assert!(s1 != s3);
    /// assert!(s3 != s1);
    /// ```
    fn eq(&self, other: &HashMultiSet<T>) -> bool {
        for val in self.distinct_elements() {
            if self.count_of(val.clone()) != other.count_of(val.clone()) {
                return false;
            };
        };
        for val in other.distinct_elements() {
            if self.count_of(val.clone()) != other.count_of(val.clone()) {
                return false;
            };
        };
        true
    }
}

impl <T> Eq for HashMultiSet<T> where T: Eq + Hash + Clone {}

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
