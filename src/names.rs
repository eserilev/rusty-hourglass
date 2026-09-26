//! A map from a name to a value, in name order.
//!
//! Every map with a name for its key goes through this type: the
//! record of a run and the vocabulary. The type holds a `BTreeMap`
//! and shows only a few operations. The Lean proofs model these
//! operations with the verified tree map of the Lean standard
//! library (`lean/Hourglass/TypesExternal.lean`), and the tests at
//! the end of this file check the laws of that model against this
//! code.
//! A new operation needs a new model and a new test, so keep the
//! list short.
//!
//! The verified code looks a name up by `&String`, not by `&str`.
//! Aeneas models a `&str` as bytes and a `String` as a Lean string,
//! so a `&str` key needs a decoder in the model and a `&String` key
//! does not.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub(crate) struct Names<V>(BTreeMap<String, V>);

impl<V> Default for Names<V> {
    fn default() -> Self {
        Names::new()
    }
}

impl<V> Names<V> {
    pub(crate) fn new() -> Self {
        Names(BTreeMap::new())
    }

    pub(crate) fn from_map(map: BTreeMap<String, V>) -> Self {
        Names(map)
    }

    pub(crate) fn into_map(self) -> BTreeMap<String, V> {
        self.0
    }

    pub(crate) fn get(&self, name: &str) -> Option<&V> {
        self.0.get(name)
    }

    /// `get`, for the verified code.
    #[allow(clippy::ptr_arg)]
    pub(crate) fn get_key(&self, name: &String) -> Option<&V> {
        self.0.get(name)
    }

    pub(crate) fn contains(&self, name: &str) -> bool {
        self.0.contains_key(name)
    }

    /// Add the name, or replace its value.
    pub(crate) fn insert(&mut self, name: String, value: V) {
        self.0.insert(name, value);
    }

    pub(crate) fn remove(&mut self, name: &str) {
        self.0.remove(name);
    }

    /// `remove`, for the verified code.
    #[allow(clippy::ptr_arg)]
    pub(crate) fn remove_key(&mut self, name: &String) {
        self.0.remove(name);
    }

    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Every name, one time each, in strictly ascending order.
    pub(crate) fn keys(&self) -> Vec<String> {
        self.0.keys().cloned().collect()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&String, &V)> {
        self.0.iter()
    }
}

/// The contract of the Lean model (`lean/Hourglass/FunsExternal.lean`).
/// The proofs trust each law below. Each test checks one law against
/// this code on random input.
#[cfg(test)]
mod tests {
    use super::Names;
    use proptest::prelude::*;

    #[derive(Debug, Clone)]
    enum Op {
        Insert(String, i64),
        RemoveKey(String),
        Remove(String),
    }

    /// Short names from a small alphabet collide often. Free strings
    /// reach every part of Unicode.
    fn name() -> impl Strategy<Value = String> {
        prop_oneof!["[ab\u{e9}\u{1F600}]{0,3}", any::<String>()]
    }

    fn op() -> impl Strategy<Value = Op> {
        prop_oneof![
            (name(), any::<i64>()).prop_map(|(k, v)| Op::Insert(k, v)),
            name().prop_map(Op::RemoveKey),
            name().prop_map(Op::Remove),
        ]
    }

    proptest! {
        /// Rust orders a `String` by its UTF-8 bytes. Lean orders it by
        /// its code points. The model needs the two orders to agree.
        #[test]
        fn byte_order_is_code_point_order(a in any::<String>(), b in any::<String>()) {
            prop_assert_eq!(a.cmp(&b), a.chars().cmp(b.chars()));
        }

        /// After any list of writes, the map holds what the model holds.
        /// The model is a list of pairs with one pair per name, the
        /// `ExtTreeMap` of the proofs in small.
        #[test]
        fn names_follows_the_model(ops in prop::collection::vec(op(), 0..40), probe in name()) {
            let mut m = Names::new();
            let mut model: Vec<(String, i64)> = Vec::new();
            for o in ops {
                match o {
                    Op::Insert(k, v) => {
                        m.insert(k.clone(), v);
                        model.retain(|(x, _)| *x != k);
                        model.push((k, v));
                    }
                    Op::RemoveKey(k) => {
                        m.remove_key(&k);
                        model.retain(|(x, _)| *x != k);
                    }
                    Op::Remove(k) => {
                        m.remove(&k);
                        model.retain(|(x, _)| *x != k);
                    }
                }
            }
            let mut probes: Vec<String> = model.iter().map(|(k, _)| k.clone()).collect();
            probes.push(probe);
            for k in &probes {
                let want = model.iter().find(|(x, _)| x == k).map(|(_, v)| *v);
                // `get_key`: the value of the name, or nothing.
                prop_assert_eq!(m.get_key(k).copied(), want);
                // The `&str` twins agree with the verified code.
                prop_assert_eq!(m.get(k).copied(), want);
                prop_assert_eq!(m.contains(k), want.is_some());
            }
            // `keys`: every name one time, in ascending code point order.
            let keys = m.keys();
            let mut want_keys: Vec<String> = model.iter().map(|(k, _)| k.clone()).collect();
            want_keys.sort_by(|a, b| a.chars().cmp(b.chars()));
            prop_assert_eq!(&keys, &want_keys);
            prop_assert_eq!(m.len(), model.len());
            prop_assert_eq!(m.is_empty(), model.is_empty());
        }
    }

    /// `new`: the empty map holds no name.
    #[test]
    fn new_holds_nothing() {
        let m: Names<i64> = Names::new();
        assert!(m.keys().is_empty());
        assert_eq!(m.get_key(&"a".to_string()), None);
        assert_eq!(m.len(), 0);
    }
}
