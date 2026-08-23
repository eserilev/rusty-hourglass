//! What the crate hands the director (spec decisions 13, 27, and
//! 41).
//!
//! Two cuts, not one. The entities are cut by what matters, and
//! they carry the PRESENT, not their history. The events are cut
//! by recency, across the whole world, and not per entity. It is
//! one snapshot plus one tail.
//!
//! The crate picks WHAT matters. The consumer writes the WORDS.
//! Sandcastle talks to a nine-year-old, maybe in Hebrew. A game
//! server talks in a fantasy register. Same data, and completely
//! different text. A crate that emits prompt text turns every
//! wording change into a crate release.
//!
//! In a small world — a game of a child with thirty entities —
//! the cut does nothing and the briefing is the whole state. The
//! cut exists for the world with five hundred.
//!
//! # The ranking is not here yet
//!
//! Salience scoring is open in the spec, so this cut takes the
//! subject first and then the newest entities. The ranking slots
//! in later, and no caller changes.

use crate::time::{EntityId, EventId};
use crate::world::World;
use serde::{Deserialize, Serialize};

/// How much of the world one briefing carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Budget {
    pub entities: usize,
    pub events: usize,
}

impl Budget {
    pub fn new(entities: usize, events: usize) -> Self {
        Budget { entities, events }
    }
}

/// The entities that matter, as they are now, and a tail of
/// recent events.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Briefing {
    pub entities: Vec<EntityId>,
    pub recent: Vec<EventId>,
}

/// Cut the world down to one briefing.
pub fn brief(world: &World, for_entity: Option<EntityId>, budget: Budget) -> Briefing {
    let mut entities: Vec<EntityId> = Vec::new();
    // The subject is always in its own briefing.
    if let Some(id) = for_entity {
        if world.entity(id).is_some() {
            entities.push(id);
        }
    }
    // Then the newest, because the newest is what the story just
    // touched. The order is the reverse of the handle, and a
    // handle only rises.
    let mut rest: Vec<EntityId> = world
        .entities()
        .map(|e| e.id)
        .filter(|id| Some(*id) != for_entity)
        .collect();
    rest.reverse();
    for id in rest {
        if entities.len() >= budget.entities {
            break;
        }
        entities.push(id);
    }
    entities.truncate(budget.entities);

    let recent = world
        .history()
        .tail(budget.events)
        .iter()
        .map(|e| e.id)
        .collect();
    Briefing { entities, recent }
}
