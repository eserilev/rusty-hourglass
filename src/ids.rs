//! A map from an entity id to a value, in id order: the entities of
//! the world.
//!
//! The type holds a `BTreeMap` and shows only a few operations, like
//! `Names`. The Lean proofs model these operations with the verified
//! tree map of the Lean standard library, keyed by the number of the
//! id (`lean/Hourglass/TypesExternal.lean`). The tests at the end of
//! this file check the laws of that model against this code. A new
//! operation needs a new model and a new test, so keep the list short.

use crate::time::EntityId;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub(crate) struct Ids<V>(BTreeMap<EntityId, V>);

impl<V> Default for Ids<V> {
    fn default() -> Self {
        Ids::new()
    }
}

impl<V> Ids<V> {
    pub(crate) fn new() -> Self {
        Ids(BTreeMap::new())
    }

    pub(crate) fn get(&self, id: EntityId) -> Option<&V> {
        self.0.get(&id)
    }

    pub(crate) fn contains(&self, id: EntityId) -> bool {
        self.0.contains_key(&id)
    }

    /// Add the id, or replace its value.
    pub(crate) fn insert(&mut self, id: EntityId, value: V) {
        self.0.insert(id, value);
    }

    /// Take the value of the id out of the map. The verified code
    /// changes a value this way: take it, change it, and insert it.
    pub(crate) fn take(&mut self, id: EntityId) -> Option<V> {
        self.0.remove(&id)
    }

    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Every id, one time each, in strictly ascending order.
    pub(crate) fn ids(&self) -> Vec<EntityId> {
        self.0.keys().copied().collect()
    }

    /// The largest id, if the map holds one.
    pub(crate) fn last_id(&self) -> Option<EntityId> {
        self.0.keys().next_back().copied()
    }

    /// Every value, in ascending id order.
    pub(crate) fn values(&self) -> impl Iterator<Item = &V> {
        self.0.values()
    }
}

/// The contract of the Lean model (`lean/Hourglass/FunsExternal.lean`).
/// The proofs trust each law below. Each test checks one law against
/// this code on random input.
#[cfg(test)]
mod tests {
    use super::Ids;
    use crate::time::EntityId;
    use proptest::prelude::*;

    #[derive(Debug, Clone)]
    enum Op {
        Insert(u32, i64),
        Take(u32),
    }

    /// Small ids collide often. Any id reaches the edges of `u32`.
    fn id() -> impl Strategy<Value = u32> {
        prop_oneof![0u32..6, any::<u32>()]
    }

    fn op() -> impl Strategy<Value = Op> {
        prop_oneof![
            (id(), any::<i64>()).prop_map(|(k, v)| Op::Insert(k, v)),
            id().prop_map(Op::Take),
        ]
    }

    proptest! {
        /// After any list of writes, the map holds what the model holds,
        /// and `take` gives the value that the model held.
        #[test]
        fn ids_follows_the_model(ops in prop::collection::vec(op(), 0..40), probe in id()) {
            let mut m = Ids::new();
            let mut model: Vec<(u32, i64)> = Vec::new();
            for o in ops {
                match o {
                    Op::Insert(k, v) => {
                        m.insert(EntityId(k), v);
                        model.retain(|(x, _)| *x != k);
                        model.push((k, v));
                    }
                    Op::Take(k) => {
                        let want = model.iter().find(|(x, _)| *x == k).map(|(_, v)| *v);
                        prop_assert_eq!(m.take(EntityId(k)), want);
                        model.retain(|(x, _)| *x != k);
                    }
                }
            }
            let mut probes: Vec<u32> = model.iter().map(|(k, _)| *k).collect();
            probes.push(probe);
            for k in probes {
                let want = model.iter().find(|(x, _)| *x == k).map(|(_, v)| *v);
                prop_assert_eq!(m.get(EntityId(k)).copied(), want);
                prop_assert_eq!(m.contains(EntityId(k)), want.is_some());
            }
            prop_assert_eq!(m.len(), model.len());
            let mut want_ids: Vec<EntityId> = model.iter().map(|(k, _)| EntityId(*k)).collect();
            want_ids.sort();
            prop_assert_eq!(m.ids(), want_ids);
            prop_assert_eq!(m.last_id(), model.iter().map(|(k, _)| EntityId(*k)).max());
            let mut pairs = model.clone();
            pairs.sort_by_key(|(k, _)| *k);
            let ordered: Vec<i64> = pairs.into_iter().map(|(_, v)| v).collect();
            let got: Vec<i64> = m.values().copied().collect();
            prop_assert_eq!(got, ordered);
        }
    }

    /// `new`: the empty map holds no id.
    #[test]
    fn new_holds_nothing() {
        let m: Ids<i64> = Ids::new();
        assert!(m.is_empty());
        assert_eq!(m.get(EntityId(0)), None);
        assert_eq!(m.last_id(), None);
    }
}
