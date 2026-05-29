//! Order-free finite maps and sets backed by `Vec`, in place of `BTreeMap`/`BTreeSet`.
//!
//! Aeneas models `Vec` and its iterator but has no model for `BTreeMap`/`BTreeSet`
//! iteration (the std B-tree iterators extract broken), so the kernel state uses these
//! wrappers. Every traversal here is an explicit index `while` loop with no early `return`,
//! no `.iter()`/`for`, and no closures -- the subset Aeneas extracts transparently. Lookups
//! are linear over the (untyped-as-set) `Vec`; the state is small, so the cost is irrelevant.
//! Keys/elements are kept unique on insert; order is not observable (all kernel uses are
//! membership / union / existential checks).

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VecMap<K, V> {
    entries: Vec<(K, V)>,
}

impl<K: Clone + PartialEq, V: Clone> VecMap<K, V> {
    pub fn new() -> Self {
        VecMap { entries: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.len() == 0
    }

    pub fn contains_key(&self, key: &K) -> bool {
        let mut found = false;
        let mut i = 0;
        while i < self.entries.len() {
            if self.entries[i].0 == *key {
                found = true;
            }
            i += 1;
        }
        found
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let mut idx = self.entries.len();
        let mut i = 0;
        while i < self.entries.len() {
            if self.entries[i].0 == *key {
                idx = i;
            }
            i += 1;
        }
        if idx < self.entries.len() {
            Some(&self.entries[idx].1)
        } else {
            None
        }
    }

    /// Insert or replace (last-write-wins, keys kept unique).
    pub fn insert(&mut self, key: K, value: V) {
        let mut idx = self.entries.len();
        let mut i = 0;
        while i < self.entries.len() {
            if self.entries[i].0 == key {
                idx = i;
            }
            i += 1;
        }
        if idx < self.entries.len() {
            self.entries[idx] = (key, value);
        } else {
            self.entries.push((key, value));
        }
    }

    /// Drop the entry for `key` if present (rebuild without it).
    pub fn remove(&mut self, key: &K) {
        let mut kept: Vec<(K, V)> = Vec::new();
        let mut i = 0;
        while i < self.entries.len() {
            if self.entries[i].0 != *key {
                kept.push(self.entries[i].clone());
            }
            i += 1;
        }
        self.entries = kept;
    }

    /// Key at position `i` (`i < len`), for explicit index-loop traversal by callers.
    pub fn key_at(&self, i: usize) -> &K {
        &self.entries[i].0
    }

    /// Value at position `i` (`i < len`), for explicit index-loop traversal by callers.
    pub fn val_at(&self, i: usize) -> &V {
        &self.entries[i].1
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VecSet<T> {
    items: Vec<T>,
}

impl<T: Clone + PartialEq> VecSet<T> {
    pub fn new() -> Self {
        VecSet { items: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.len() == 0
    }

    pub fn contains(&self, x: &T) -> bool {
        let mut found = false;
        let mut i = 0;
        while i < self.items.len() {
            if self.items[i] == *x {
                found = true;
            }
            i += 1;
        }
        found
    }

    /// Insert if absent (elements kept unique).
    pub fn insert(&mut self, x: T) {
        if !self.contains(&x) {
            self.items.push(x);
        }
    }

    /// Drop `x` if present (rebuild without it).
    pub fn remove(&mut self, x: &T) {
        let mut kept: Vec<T> = Vec::new();
        let mut i = 0;
        while i < self.items.len() {
            if self.items[i] != *x {
                kept.push(self.items[i].clone());
            }
            i += 1;
        }
        self.items = kept;
    }

    /// Element at position `i` (`i < len`), for explicit index-loop traversal by callers.
    pub fn at(&self, i: usize) -> &T {
        &self.items[i]
    }

    /// In-place union: insert every element of `other`.
    pub fn union_with(&mut self, other: &VecSet<T>) {
        let mut i = 0;
        while i < other.items.len() {
            self.insert(other.items[i].clone());
            i += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_insert_get_contains() {
        let mut m: VecMap<String, u32> = VecMap::new();
        assert!(m.is_empty());
        m.insert("a".to_string(), 1);
        m.insert("b".to_string(), 2);
        assert_eq!(m.len(), 2);
        assert!(m.contains_key(&"a".to_string()));
        assert_eq!(m.get(&"b".to_string()), Some(&2));
        assert_eq!(m.get(&"z".to_string()), None);
    }

    #[test]
    fn map_insert_is_last_write_wins_and_unique() {
        let mut m: VecMap<String, u32> = VecMap::new();
        m.insert("a".to_string(), 1);
        m.insert("a".to_string(), 9);
        assert_eq!(m.len(), 1);
        assert_eq!(m.get(&"a".to_string()), Some(&9));
    }

    #[test]
    fn map_remove() {
        let mut m: VecMap<String, u32> = VecMap::new();
        m.insert("a".to_string(), 1);
        m.insert("b".to_string(), 2);
        m.remove(&"a".to_string());
        assert!(!m.contains_key(&"a".to_string()));
        assert!(m.contains_key(&"b".to_string()));
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn map_index_access() {
        let mut m: VecMap<String, u32> = VecMap::new();
        m.insert("a".to_string(), 1);
        assert_eq!(m.key_at(0), &"a".to_string());
        assert_eq!(m.val_at(0), &1);
    }

    #[test]
    fn set_insert_contains_unique() {
        let mut s: VecSet<u32> = VecSet::new();
        assert!(s.is_empty());
        s.insert(1);
        s.insert(1);
        s.insert(2);
        assert_eq!(s.len(), 2);
        assert!(s.contains(&1));
        assert!(!s.contains(&3));
    }

    #[test]
    fn set_remove_and_union() {
        let mut a: VecSet<u32> = VecSet::new();
        a.insert(1);
        a.insert(2);
        a.remove(&1);
        assert!(!a.contains(&1));

        let mut b: VecSet<u32> = VecSet::new();
        b.insert(2);
        b.insert(3);
        a.union_with(&b);
        assert!(a.contains(&2));
        assert!(a.contains(&3));
        assert_eq!(a.len(), 2);
    }
}
