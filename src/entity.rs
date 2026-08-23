//! One person, place, thing, or faction (spec decisions 4, 5, and
//! 15).
//!
//! An entity carries a name a person reads, a type from a closed
//! list, how long it has been here, and its facts. Where it sits
//! is a fact and not a field, so "where was Ada when the mill
//! burned" has an answer (spec decision 32).
//!
//! An entity stays in the state after it dies. The history names
//! it, and other facts point at it. Only its `existence` closes.

use crate::fact::{Fact, LOCATED_IN};
use crate::time::{EntityId, Tick, TimeSpan};
use serde::{Deserialize, Serialize};

/// What an entity is. A closed list, so a rule can refuse "the
/// sword died" and "the faction is in the mill".
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum EntityType {
    Person,
    Place,
    Thing,
    Faction,
}

impl EntityType {
    pub fn label(&self) -> &'static str {
        match self {
            EntityType::Person => "person",
            EntityType::Place => "place",
            EntityType::Thing => "thing",
            EntityType::Faction => "faction",
        }
    }

    /// Every type, in one order on every machine.
    pub fn all() -> [EntityType; 4] {
        [
            EntityType::Person,
            EntityType::Place,
            EntityType::Thing,
            EntityType::Faction,
        ]
    }
}

/// One person, place, thing, or faction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Entity {
    pub id: EntityId,
    pub entity_type: EntityType,
    pub name: String,
    /// Started, and maybe ended. One span, ever.
    pub existence: TimeSpan,
    /// Everything true of it right now, including where it sits.
    pub facts: Vec<Fact>,
}

impl Entity {
    pub fn new(id: EntityId, entity_type: EntityType, name: &str, from: Tick) -> Self {
        Entity {
            id,
            entity_type,
            name: name.to_string(),
            existence: TimeSpan::open(from),
            facts: Vec::new(),
        }
    }

    /// Is this entity gone? A gone entity gains no facts.
    pub fn gone(&self) -> bool {
        self.existence.ended()
    }

    /// The fact in one slot: this name, and this target.
    pub fn fact(&self, name: &str, linked_to: Option<EntityId>) -> Option<&Fact> {
        self.facts.iter().find(|f| f.same_slot(name, linked_to))
    }

    /// Every open fact of one name. A name with `targets: Many`
    /// holds several: Ada hates Bren, and Ada hates Cole.
    pub fn facts_named<'a>(&'a self, name: &'a str) -> impl Iterator<Item = &'a Fact> {
        self.facts.iter().filter(move |f| f.name == name)
    }

    /// Does one fact of this name hold, whatever its target?
    pub fn has(&self, name: &str) -> bool {
        self.facts.iter().any(|f| f.name == name)
    }

    /// The number one solo fact carries.
    pub fn value(&self, name: &str) -> Option<i64> {
        self.fact(name, None).and_then(|f| f.value)
    }

    /// Where this entity sits right now. `located_in` allows one
    /// target at a time, so at most one fact answers.
    pub fn location(&self) -> Option<EntityId> {
        self.facts
            .iter()
            .find(|f| f.name == LOCATED_IN)
            .and_then(|f| f.linked_to)
    }
}
