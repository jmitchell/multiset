fn main() {
    let btree_multiset_code = std::fs::read_to_string("./src/hash_multiset.rs")
        .expect("Could not open hash_multiset source file")
        .replace("Hash + Eq", "Ord")
        .replace("Eq + Hash", "Ord")
        .replace("hash_map::", "btree_map::")
        .replace("HashMap", "BTreeMap")
        .replace("HashMultiSet", "BTreeMultiSet")
        .replace("use std::hash::Hash;\n", "")
        .replace("hash-based multiset", "tree-based multiset");
    std::fs::write("./src/btree_multiset.rs", btree_multiset_code.as_bytes())
        .expect("Could not write btree_multiset file");
    println!("cargo:rerun-if-changed=./src/hash_multiset.rs");
}
