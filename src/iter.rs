// Copyright 2019 multiset developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
#![warn(missing_docs)]

use std::borrow::Borrow;
use std::marker::PhantomData;

/// An iterator over the items of a `MultiSet`.
///
/// This `struct` is created by the [`iter`](super::HashMultiSet::iter) method on
/// [`HashMultiSet`](super::HashMultiSet) or [`BTreeMultiSet`](super::BTreeMultiSet).
pub struct Iter<K: Clone, V: Borrow<usize>, InnerIter: Iterator<Item = (K, V)>> {
    pub(crate) iter: InnerIter,
    pub(crate) duplicate: Option<<InnerIter as Iterator>::Item>,
    pub(crate) duplicate_index: usize,
    pub(crate) _ghost: PhantomData<*const (K, V)>,
}

impl<K: Clone, V: Borrow<usize>, InnerIter: Iterator<Item = (K, V)> + Clone> Clone
    for Iter<K, V, InnerIter>
where
    <InnerIter as Iterator>::Item: Clone,
{
    fn clone(&self) -> Iter<K, V, InnerIter> {
        Iter {
            iter: self.iter.clone(),
            duplicate: self.duplicate.clone(),
            duplicate_index: self.duplicate_index,
            _ghost: PhantomData,
        }
    }
}

impl<K: Clone, V: Borrow<usize>, InnerIter: Iterator<Item = (K, V)>> Iterator
    for Iter<K, V, InnerIter>
{
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        if self.duplicate.is_none() {
            self.duplicate = self.iter.next();
        }
        if let Some((key, count)) = self.duplicate.as_ref() {
            self.duplicate_index += 1;
            let key = key.clone();
            if &self.duplicate_index >= count.borrow() {
                self.duplicate = None;
                self.duplicate_index = 0;
            }
            Some(key)
        } else {
            None
        }
    }
}
