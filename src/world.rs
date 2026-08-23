//! The world: the history, the derived state, and the one writer
//! (spec decisions 10 to 12, 17, 30, and 32).
//!
//! ```text
//! EventHistory                        the truth. append-only, ordered.
//!    |
//!    |  apply, one event at a time
//!    v
//! state    BTreeMap<EntityId, Entity>  derived. entities, each with facts.
//! ```
//!
//! `apply` is the only writer. Nothing sets a fact directly.
//! Break that, and the history and the state drift apart, and
//! then neither one is worth trusting.
//!
//! `apply` TRUSTS what it is given. `validate` is the gate, and
//! [`World::propose`] runs both. [`World::commit`] runs `apply`
//! alone, for a caller that already checked, and for a test that
//! builds a state on purpose.
//!
//! # The same events always give the same state
//!
//! Five things break that, and the crate holds none of them: no
//! unordered collection, no float, no system clock, no unseeded
//! random source, and nothing outside the two arguments.
//!
//! # One fact per slot
//!
//! A slot is a name and a target together. `FactStart` closes the
//! fact in the slot it fills, so a mill cannot be burned twice at
//! once, and Ada can still hate two people.
//!
//! A `located_in` allows one target at a time, so a move must
//! close a fact in ANOTHER slot. That happens when, and only
//! when, the count on the target side is exactly one: then there
//! is one fact to close and no choice about which. A count of
//! twelve leaves a choice, so the crate refuses instead of
//! guessing (`TooManyTargets`).

use crate::brief::{Briefing, Budget};
use crate::entity::{Entity, EntityType};
use crate::event::{Event, EventHistory, EventKind};
use crate::fact::{Count, Fact, FactRules, FactVocabulary, LOCATED_IN};
use crate::reject::Rejection;
use crate::time::{EntityId, EventId, Tick};
use crate::validate;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

/// The hop cap of a walk up the location chain. A sound world
/// never reaches it, because `validate` refuses a cycle. A world
/// built by `commit` alone can hold one, so every walk stops.
pub const MAX_HOPS: usize = 1024;

/// The tick, the vocabulary, the entities, and the history. The
/// whole thing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct World {
    pub tick: Tick,
    pub vocabulary: FactVocabulary,
    entities: BTreeMap<EntityId, Entity>,
    history: EventHistory,
}

impl World {
    pub fn new(vocabulary: FactVocabulary) -> Self {
        World {
            tick: Tick(0),
            vocabulary,
            entities: BTreeMap::new(),
            history: EventHistory::new(),
        }
    }

    pub fn entity(&self, id: EntityId) -> Option<&Entity> {
        self.entities.get(&id)
    }

    /// Every entity, in one order on every machine.
    pub fn entities(&self) -> impl Iterator<Item = &Entity> {
        self.entities.values()
    }

    pub fn len(&self) -> usize {
        self.entities.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entities.is_empty()
    }

    pub fn history(&self) -> &EventHistory {
        &self.history
    }

    /// The handle the next `EntityCreated` takes. An id is never
    /// reused, so the count only rises.
    pub fn next_entity_id(&self) -> EntityId {
        EntityId(
            self.entities
                .keys()
                .next_back()
                .map(|k| k.0 + 1)
                .unwrap_or(0),
        )
    }

    // -----------------------------------------------------------
    // The two ways in
    // -----------------------------------------------------------

    /// Check the event, then fold it in. Every reason comes back
    /// at once, so one retry fixes everything.
    pub fn propose(&mut self, tick: Tick, kind: EventKind) -> Result<EventId, Vec<Rejection>> {
        let faults = validate::validate(self, tick, &kind);
        if !faults.is_empty() {
            return Err(faults);
        }
        Ok(self.commit(tick, kind))
    }

    /// Propose several events at one tick. Each one stands alone:
    /// the good ones land, and only the bad ones come back. A bad
    /// proposal costs one event, never the whole tick.
    pub fn propose_all(
        &mut self,
        tick: Tick,
        kinds: Vec<EventKind>,
    ) -> Vec<Result<EventId, Vec<Rejection>>> {
        kinds
            .into_iter()
            .map(|kind| self.propose(tick, kind))
            .collect()
    }

    /// Fold an event in with no check. The caller carries the
    /// promise that it is legal.
    pub fn commit(&mut self, tick: Tick, kind: EventKind) -> EventId {
        let id = self.history.push(tick, kind);
        let event = self.history.get(id).expect("the push just landed").clone();
        self.fold(&event);
        if tick > self.tick {
            self.tick = tick;
        }
        id
    }

    // -----------------------------------------------------------
    // The only writer
    // -----------------------------------------------------------

    fn fold(&mut self, event: &Event) {
        match &event.kind {
            EventKind::EntityCreated {
                id,
                entity_type,
                name,
            } => {
                self.entities
                    .entry(*id)
                    .or_insert_with(|| Entity::new(*id, *entity_type, name, event.tick));
            }
            EventKind::EntityDestroyed { id } => {
                if let Some(entity) = self.entities.get_mut(id) {
                    // The entity stays. The history names it, and
                    // other facts point at it. Only the span
                    // closes, and the facts stay, because a grudge
                    // outlives the person and a crown does not
                    // (spec decision 9).
                    if entity.existence.until.is_none() {
                        entity.existence.until = Some(event.tick);
                    }
                }
            }
            EventKind::FactStart {
                entity,
                name,
                value,
                linked_to,
            } => {
                let wide = self.single_target(name);
                if let Some(row) = self.entities.get_mut(entity) {
                    if wide {
                        row.facts.retain(|f| f.name != *name);
                    } else {
                        row.facts.retain(|f| !f.same_slot(name, *linked_to));
                    }
                    row.facts.push(Fact {
                        name: name.clone(),
                        value: *value,
                        linked_to: *linked_to,
                        opened: event.id,
                    });
                }
            }
            EventKind::FactUpdate {
                entity,
                name,
                linked_to,
                to,
                ..
            } => {
                if let Some(row) = self.entities.get_mut(entity) {
                    if let Some(fact) = row.facts.iter_mut().find(|f| f.same_slot(name, *linked_to))
                    {
                        // A new value is a new fact (spec decision
                        // 15), so `opened` moves to this event.
                        fact.value = Some(*to);
                        fact.opened = event.id;
                    }
                }
            }
            EventKind::FactEnd {
                entity,
                name,
                linked_to,
            } => {
                if let Some(row) = self.entities.get_mut(entity) {
                    row.facts.retain(|f| !f.same_slot(name, *linked_to));
                }
            }
        }
    }

    /// Does this name allow one target at a time? An undeclared
    /// name does not, so an unknown name closes its own slot only.
    fn single_target(&self, name: &str) -> bool {
        match self.vocabulary.rules(name) {
            Some(FactRules::Linked { targets, .. }) => targets.is_single(),
            _ => false,
        }
    }

    // -----------------------------------------------------------
    // Replay and rollback
    // -----------------------------------------------------------

    /// Build a state from nothing. The same history builds the
    /// same state, on any machine, in any run.
    ///
    /// `replay` does NOT run `validate` again. Every event in the
    /// history passed it once, and a rule added in year two must
    /// never stop an old history from replaying. The migration
    /// rules hold the other half of that promise: the rules of a
    /// declared name never change (see `migrate`).
    pub fn replay(vocabulary: FactVocabulary, history: &EventHistory) -> World {
        let mut world = World::new(vocabulary);
        for event in history.iter() {
            world.history.push(event.tick, event.kind.clone());
            world.fold(event);
            if event.tick > world.tick {
                world.tick = event.tick;
            }
        }
        world
    }

    /// Cut the history and build the state again. This is the
    /// undo of a child, and it costs nothing, because `apply`
    /// builds the state from nothing.
    pub fn rewind(&mut self, after: EventId) {
        self.history.truncate(after);
        let history = std::mem::take(&mut self.history);
        let vocabulary = self.vocabulary.clone();
        *self = World::replay(vocabulary, &history);
    }

    // -----------------------------------------------------------
    // The containment queries (spec decision 32)
    // -----------------------------------------------------------

    /// Who is in there, in one order on every machine.
    pub fn contents(&self, place: EntityId) -> Vec<EntityId> {
        self.entities
            .values()
            .filter(|e| e.location() == Some(place))
            .map(|e| e.id)
            .collect()
    }

    /// The mill, then Ashford. The walk stops at a ring, so a
    /// world built by `commit` alone still answers.
    pub fn ancestry(&self, id: EntityId) -> Vec<EntityId> {
        let mut out = Vec::new();
        let mut seen = BTreeSet::new();
        seen.insert(id);
        let mut at = id;
        for _ in 0..MAX_HOPS {
            let Some(up) = self.entities.get(&at).and_then(|e| e.location()) else {
                break;
            };
            if !seen.insert(up) {
                break;
            }
            out.push(up);
            at = up;
        }
        out
    }

    /// Would this move put a place inside itself? The answer
    /// names the entity on the chain that already sits inside the
    /// one that is moving.
    pub fn would_cycle(&self, entity: EntityId, target: EntityId) -> Option<EntityId> {
        let mut at = target;
        let mut seen = BTreeSet::new();
        for _ in 0..MAX_HOPS {
            if at == entity {
                return Some(at);
            }
            if !seen.insert(at) {
                return None;
            }
            at = self.entities.get(&at).and_then(|e| e.location())?;
        }
        None
    }

    /// Every fact anywhere that points at this entity, with the
    /// entity that holds it. The reverse of a link.
    pub fn facts_linked_to(&self, target: EntityId) -> Vec<(EntityId, &Fact)> {
        let mut out = Vec::new();
        for entity in self.entities.values() {
            for fact in &entity.facts {
                if fact.linked_to == Some(target) {
                    out.push((entity.id, fact));
                }
            }
        }
        out
    }

    /// The entities that hold one name about one target.
    pub fn holders_of(&self, name: &str, target: EntityId) -> Vec<EntityId> {
        self.entities
            .values()
            .filter(|e| {
                e.facts
                    .iter()
                    .any(|f| f.name == name && f.linked_to == Some(target))
            })
            .map(|e| e.id)
            .collect()
    }

    /// The targets one entity holds one name about.
    pub fn targets_of(&self, name: &str, holder: EntityId) -> Vec<EntityId> {
        match self.entities.get(&holder) {
            None => Vec::new(),
            Some(entity) => entity
                .facts
                .iter()
                .filter(|f| f.name == name)
                .filter_map(|f| f.linked_to)
                .collect(),
        }
    }

    /// Did this slot ever leave the state? The answer lives in
    /// the history, because the state holds the present alone.
    pub fn ever_ended(&self, entity: EntityId, name: &str) -> bool {
        self.history.iter().any(|e| {
            matches!(&e.kind, EventKind::FactEnd { entity: who, name: what, .. }
                if *who == entity && what == name)
        })
    }

    /// The type of one entity, for the type map of a link.
    pub fn type_of(&self, id: EntityId) -> Option<EntityType> {
        self.entities.get(&id).map(|e| e.entity_type)
    }

    /// The place a name reserves. `located_in` is the one name
    /// the crate declares, so the crate answers this itself.
    pub fn location_of(&self, id: EntityId) -> Option<EntityId> {
        self.entities.get(&id).and_then(|e| e.location())
    }

    /// What the crate hands the director: the entities that
    /// matter, and a tail of recent events (spec decision 41).
    pub fn brief(&self, for_entity: Option<EntityId>, budget: Budget) -> Briefing {
        crate::brief::brief(self, for_entity, budget)
    }

    /// The flat cut of this entity: its solo facts, as a memory
    /// record.
    pub fn record(&self, entity: EntityId) -> crate::memory::Record {
        crate::memory::record(self, entity)
    }

    /// The name the crate reserves for a location.
    pub fn located_in(&self) -> &'static str {
        LOCATED_IN
    }

    /// The count on the target side of one name, for a caller
    /// that builds a move.
    pub fn target_count(&self, name: &str) -> Option<Count> {
        match self.vocabulary.rules(name) {
            Some(FactRules::Linked { targets, .. }) => Some(*targets),
            _ => None,
        }
    }
}
