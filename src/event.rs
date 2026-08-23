//! The history: five event kinds, and a list that only grows
//! (spec decisions 10, 30, and 31).
//!
//! The history is the truth. The state is derived from it, so an
//! event is the only way anything changes. Nothing is edited, and
//! nothing is removed.
//!
//! One method shortens the history, and it is named so it cannot
//! happen by accident. The undo of a child cuts the history and
//! replays it, which is why `truncate` exists at all.

use crate::entity::EntityType;
use crate::time::{EntityId, EventId, Tick};
use serde::{Deserialize, Serialize};

/// One entry in the history.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Event {
    pub id: EventId,
    pub tick: Tick,
    pub kind: EventKind,
}

/// The five things that can happen. A closed list, so a director
/// can never invent a change nobody wrote a rule for.
///
/// Moving is not here. Location is a fact, so a move is a
/// `FactStart` (spec decision 32). A type never changes, and a
/// name never changes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EventKind {
    EntityCreated {
        id: EntityId,
        entity_type: EntityType,
        name: String,
    },
    EntityDestroyed {
        id: EntityId,
    },
    FactStart {
        entity: EntityId,
        name: String,
        value: Option<i64>,
        linked_to: Option<EntityId>,
    },
    FactUpdate {
        entity: EntityId,
        name: String,
        linked_to: Option<EntityId>,
        from: i64,
        to: i64,
    },
    FactEnd {
        entity: EntityId,
        name: String,
        linked_to: Option<EntityId>,
    },
}

impl EventKind {
    /// The entity this event acts on.
    pub fn subject(&self) -> EntityId {
        match self {
            EventKind::EntityCreated { id, .. } => *id,
            EventKind::EntityDestroyed { id } => *id,
            EventKind::FactStart { entity, .. } => *entity,
            EventKind::FactUpdate { entity, .. } => *entity,
            EventKind::FactEnd { entity, .. } => *entity,
        }
    }

    /// The fact name this event acts on, when it acts on one.
    /// Founding an entity does not.
    pub fn fact_name(&self) -> Option<&str> {
        match self {
            EventKind::FactStart { name, .. }
            | EventKind::FactUpdate { name, .. }
            | EventKind::FactEnd { name, .. } => Some(name.as_str()),
            _ => None,
        }
    }

    /// The word a rejection carries.
    pub fn label(&self) -> &'static str {
        match self {
            EventKind::EntityCreated { .. } => "entity created",
            EventKind::EntityDestroyed { .. } => "entity destroyed",
            EventKind::FactStart { .. } => "fact start",
            EventKind::FactUpdate { .. } => "fact update",
            EventKind::FactEnd { .. } => "fact end",
        }
    }
}

/// Every event, in order. Append-only by construction.
///
/// There is no `remove`, no `clear`, and no way to reach inside.
/// The guarantee lives on the type, so it holds wherever the
/// value goes.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct EventHistory(Vec<Event>);

impl EventHistory {
    pub fn new() -> Self {
        EventHistory(Vec::new())
    }

    /// The only way in. The history hands out the id it gave.
    pub fn push(&mut self, tick: Tick, kind: EventKind) -> EventId {
        let id = self.next_id();
        self.0.push(Event { id, tick, kind });
        id
    }

    pub fn get(&self, id: EventId) -> Option<&Event> {
        self.0.get(id.0 as usize).filter(|e| e.id == id)
    }

    /// The last `n` events, anywhere in the world.
    pub fn tail(&self, n: usize) -> &[Event] {
        let start = self.0.len().saturating_sub(n);
        &self.0[start..]
    }

    pub fn next_id(&self) -> EventId {
        EventId(self.0.len() as u64)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Event> {
        self.0.iter()
    }

    /// The tick of the last event, or zero on an empty history.
    pub fn last_tick(&self) -> Tick {
        self.0.last().map(|e| e.tick).unwrap_or(Tick(0))
    }

    /// The one way to shorten the history, for rollback. Every
    /// event up to and including `after` stays.
    pub fn truncate(&mut self, after: EventId) {
        let keep = (after.0 as usize).saturating_add(1);
        if keep < self.0.len() {
            self.0.truncate(keep);
        }
    }
}

impl<'a> IntoIterator for &'a EventHistory {
    type Item = &'a Event;
    type IntoIter = std::slice::Iter<'a, Event>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}
