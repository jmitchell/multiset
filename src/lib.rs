// Copyright 2019 multiset developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A multiset is an unordered collection of values. They are also
//! known as bags.
//!
//! Unlike sets where each value is either included or not, multisets
//! permit duplicates. Consequently, they're useful for maintaining a
//! count of distinct values.

mod btree_multiset;
mod hash_multiset;
mod iter;

pub use btree_multiset::BTreeMultiSet;
pub use hash_multiset::HashMultiSet;
pub use iter::Iter;
