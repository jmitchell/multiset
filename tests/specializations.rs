#[macro_use]
extern crate quickcheck;

use std::fmt::Debug;
use std::ops::BitXor;

struct Unspecialized<I>(I);
impl<I> Iterator for Unspecialized<I>
where
    I: Iterator,
{
    type Item = I::Item;

    #[inline(always)]
    fn next(&mut self) -> Option<I::Item> {
        self.0.next()
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

fn check_specialized<'a, V, IterItem, Iter, F>(iterator: &Iter, mapper: F)
where
    V: Eq + Debug,
    IterItem: 'a,
    Iter: Iterator<Item = IterItem> + Clone + 'a,
    F: Fn(Box<dyn Iterator<Item = IterItem> + 'a>) -> V,
{
    assert_eq!(
        mapper(Box::new(Unspecialized(iterator.clone()))),
        mapper(Box::new(iterator.clone()))
    )
}

fn check_specialized_count_last_nth_sizeh<'a, IterItem, Iter>(
    it: &Iter,
    known_expected_size: Option<usize>,
) where
    IterItem: 'a + Eq + Debug,
    Iter: Iterator<Item = IterItem> + Clone + 'a,
{
    let size = it.clone().count();
    if let Some(expected_size) = known_expected_size {
        assert_eq!(size, expected_size);
    }
    check_specialized(it, |i| i.count());
    check_specialized(it, |i| i.last());
    for n in 0..size + 2 {
        check_specialized(it, |mut i| i.nth(n));
    }
    let mut it_sh = it.clone();
    for n in 0..size + 2 {
        let len = it_sh.clone().count();
        let (min, max) = it_sh.size_hint();
        assert_eq!((size - n.min(size)), len);
        assert!(min <= len);
        if let Some(max) = max {
            assert!(len <= max);
        }
        it_sh.next();
    }
}

fn check_specialized_fold_xor<'a, IterItem, Iter>(it: &Iter)
where
    IterItem: 'a
        + BitXor
        + Eq
        + Debug
        + BitXor<<IterItem as BitXor>::Output, Output = <IterItem as BitXor>::Output>
        + Clone,
    <IterItem as BitXor>::Output:
        BitXor<Output = <IterItem as BitXor>::Output> + Eq + Debug + Clone,
    Iter: Iterator<Item = IterItem> + Clone + 'a,
{
    check_specialized(it, |mut i| {
        let first = i.next().map(|f| f.clone() ^ (f.clone() ^ f));
        i.fold(first, |acc, v: IterItem| acc.map(move |a| v ^ a))
    });
}

fn hms_test(test_vec: Vec<i32>, known_expected_size: Option<usize>) {
    let hms: multiset::HashMultiSet<_> = test_vec.into_iter().collect();
    let iter = hms.iter();
    check_specialized_count_last_nth_sizeh(&iter, known_expected_size.map(|x| x + 1));
    check_specialized_fold_xor(&iter)
}

quickcheck! {
    fn hms_test_qc(test_vec: Vec<i32>) -> () {
        hms_test(test_vec, None)
    }
}
