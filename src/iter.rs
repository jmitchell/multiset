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
    pub(crate) duplicate_back: Option<<InnerIter as Iterator>::Item>,
    pub(crate) duplicate_index_back: usize,
    pub(crate) len: usize,
    pub(crate) _ghost: PhantomData<*const (K, V)>,
}

impl<K: Clone, V: Borrow<usize>, InnerIter: Iterator<Item = (K, V)> + ExactSizeIterator>
    Iter<K, V, InnerIter>
{
    pub(crate) fn new(iter: InnerIter, len: usize) -> Self {
        Iter {
            iter,
            duplicate: None,
            duplicate_index: 0,
            duplicate_back: None,
            duplicate_index_back: 0,
            len,
            _ghost: PhantomData,
        }
    }
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
            duplicate_back: self.duplicate_back.clone(),
            duplicate_index_back: self.duplicate_index_back,
            len: self.len,
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
            if self.duplicate_index >= *count.borrow() {
                self.duplicate = None;
                self.duplicate_index = 0;
            }
            self.len -= 1;
            Some(key)
        } else {
            if let Some((key, count)) = self.duplicate_back.as_ref() {
                self.duplicate_index_back += 1;
                let key = key.clone();
                if self.duplicate_index_back >= *count.borrow() {
                    self.duplicate_back = None;
                }
                self.len -= 1;
                Some(key)
            } else {
                None
            }
        }
    }

    fn count(self) -> usize {
        self.len()
    }

    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        let duplicate_index = self.duplicate_index;
        let duplicate_index_back = self.duplicate_index_back;
        self.duplicate
            .map(move |(val, count)| (val, *count.borrow() - duplicate_index))
            .into_iter()
            .chain(self.iter.map(move |(val, count)| (val, *count.borrow())))
            .chain(
                self.duplicate_back
                    .map(move |(val, count)| (val, *count.borrow() - duplicate_index_back))
                    .into_iter(),
            )
            .fold(init, move |acc, (val, count)| {
                (0..count).fold(acc, |acc, _| f(acc, val.clone()))
            })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let l = self.len();
        (l, Some(l))
    }
}

impl<K: Clone, V: Borrow<usize>, InnerIter: Iterator<Item = (K, V)>> ExactSizeIterator
    for Iter<K, V, InnerIter>
{
    fn len(&self) -> usize {
        self.len
    }
}

impl<K: Clone, V: Borrow<usize>, InnerIter: Iterator<Item = (K, V)> + DoubleEndedIterator>
    DoubleEndedIterator for Iter<K, V, InnerIter>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.duplicate_back.is_none() {
            self.duplicate_back = self.iter.next_back();
        }
        if let Some((key, count)) = self.duplicate_back.as_ref() {
            self.duplicate_index_back += 1;
            let key = key.clone();
            if self.duplicate_index_back >= *count.borrow() {
                self.duplicate_back = None;
                self.duplicate_index_back = 0;
            }
            self.len -= 1;
            Some(key)
        } else {
            if let Some((key, count)) = self.duplicate.as_ref() {
                self.duplicate_index += 1;
                let key = key.clone();
                if self.duplicate_index >= *count.borrow() {
                    self.duplicate = None;
                }
                self.len -= 1;
                Some(key)
            } else {
                None
            }
        }
    }

    fn rfold<B, F>(self, init: B, mut f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        let duplicate_index = self.duplicate_index;
        let duplicate_index_back = self.duplicate_index_back;
        self.duplicate_back
            .map(move |(val, count)| (val, *count.borrow() - duplicate_index_back))
            .into_iter()
            .chain(
                self.iter
                    .rev()
                    .map(move |(val, count)| (val, *count.borrow())),
            )
            .chain(
                self.duplicate
                    .map(move |(val, count)| (val, *count.borrow() - duplicate_index))
                    .into_iter(),
            )
            .fold(init, move |acc, (val, count)| {
                (0..count).fold(acc, |acc, _| f(acc, val.clone()))
            })
    }
}

impl<K: Clone, V: Borrow<usize>, InnerIter: Iterator<Item = (K, V)> + std::iter::FusedIterator>
    std::iter::FusedIterator for Iter<K, V, InnerIter>
{
}
