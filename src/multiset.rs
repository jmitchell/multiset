use std::collections::{HashMap};
use std::collections::hash_map::{Entry,Keys};
use std::hash::{Hash};
use std::ops::{Add};

/// A hash-based multiset.
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

    /// Creates a new `HashMultiSet` from the elements in a `Vec`.
    ///
    /// # Examples
    ///
    /// Count occurrences of each `char` in `"hello world"`:
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let vals = vec!['h','e','l','l','o',' ','w','o','r','l','d'];
    /// let multiset = HashMultiSet::from_vec(vals);
    /// ```
    pub fn from_vec(v: Vec<K>) -> Self {
        let mut multiset = HashMultiSet::new();
        for elem in v {
            multiset.insert(elem);
        }
        multiset
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
    ///
    /// let multiset = HashMultiSet::from_vec(vec![1,1,2]);
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
    ///
    /// let multiset = HashMultiSet::from_vec(vec![1,1,2]);
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
    /// Insert `1` into a new `HashMultiSet`:
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let mut multiset: HashMultiSet<i32> = HashMultiSet::new();
    /// multiset.insert(1);
    /// ```
    pub fn insert(&mut self, val: K) {
        match self.elem_counts.entry(val) {
            Entry::Vacant(view) => {
                view.insert(1);
            },
            Entry::Occupied(mut view) => {
                let v = view.get_mut();
                *v += 1;
            }
        }
    }

    /// Counts the occurrences of `val`.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    ///
    /// let vals = vec!['h','e','l','l','o',' ','w','o','r','l','d'];
    /// let multiset = HashMultiSet::from_vec(vals);
    /// assert_eq!(1, multiset.count_of('h'));
    /// assert_eq!(3, multiset.count_of('l'));
    /// assert_eq!(0, multiset.count_of('z'));
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
    ///
    /// let combined = HashMultiSet::from_vec(vec![1,2,3]) + HashMultiSet::from_vec(vec![1,1,4]);
    /// assert_eq!(3, combined.count_of(1));
    /// assert_eq!(1, combined.count_of(2));
    /// assert_eq!(1, combined.count_of(3));
    /// assert_eq!(1, combined.count_of(4));
    /// assert_eq!(0, combined.count_of(5));
    /// ```
    fn add(self, rhs: HashMultiSet<T>) ->  HashMultiSet<T> {
        let mut ret: HashMultiSet<T> = HashMultiSet::new();
        for val in self.distinct_elements() {
            for _ in 0..(self.count_of((*val).clone())) {
                ret.insert((*val).clone());
            }
        }
        for val in rhs.distinct_elements() {
            for _ in 0..(rhs.count_of((*val).clone())) {
                ret.insert((*val).clone());
            }
        }
        ret
    }
}
