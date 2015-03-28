#![allow(dead_code)]

use std::collections::{HashMap};
use std::collections::hash_map::{Entry};
use std::hash::{Hash};

struct MultiSet<K> {
    elem_counts: HashMap<K, usize>
}

impl<K> MultiSet<K> where
    K: Eq + Hash + Clone
{
    fn new() -> Self {
        MultiSet { elem_counts: HashMap::new() }
    }

    fn total_elements(&self) -> usize {
        self.elem_counts
            .values()
            .fold(0, |a,b| a + *b)
    }

    fn distinct_elements(&self) -> Vec<K> {
        // TODO: try refactoring to avoid clone
        self.elem_counts
            .keys()
            .map(|x| (*x).clone())
            .collect()
    }

    fn add(&mut self, val: K) {
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

    fn count_of(&self, val: K) -> usize {
        self.elem_counts
            .get(&val)
            .map_or(0, |x| *x)
    }

    fn from_vec(v: Vec<K>) -> Self {
        let mut multiset = MultiSet::new();
        for elem in v {
            multiset.add(elem);
        }
        multiset
    }
}

#[cfg(test)]
mod tests {
    use super::{MultiSet};

    #[test]
    fn new_multiset_is_empty() {
        let multiset: MultiSet<char> = MultiSet::new();

        assert_eq!(0, multiset.total_elements());
        assert_eq!(0, multiset.distinct_elements().len());
    }

    #[test]
    fn multiset_with_one_element() {
        let mut multiset: MultiSet<char> = MultiSet::new();
        multiset.add('a');

        assert_eq!(1, multiset.total_elements());
        assert_eq!(1, multiset.distinct_elements().len());
        assert_eq!(1, multiset.count_of('a'));
        assert_eq!(0, multiset.count_of('z'));
    }

    #[test]
    fn multiset_from_vec() {
        let v = vec!['a', 'b', 'c',
                     'a',      'c',
                     'a'          ];
        let ms = MultiSet::from_vec(v);

        assert_eq!(3, ms.count_of('a'));
        assert_eq!(1, ms.count_of('b'));
        assert_eq!(2, ms.count_of('c'));
    }
}
