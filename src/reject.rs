//! Why a proposal was refused (spec decisions 35 to 40).
//!
//! `Malformed` is wrong on its own: the check needs the
//! vocabulary and nothing else. A `Malformed` means the PROMPT
//! failed, because decision 34 put the whole vocabulary in front
//! of the model and the model ignored it.
//!
//! `Contradiction` is fine on its own, and the world is in the
//! way. Ashford already has a king. Ada is dead. A
//! `Contradiction` means the model was reasonable and the world
//! moved, so a retry with fresh context is the answer.
//!
//! Two faults, two responses, so two types.
//!
//! A refusal carries EVERY reason at once, so one retry fixes
//! everything. A rejection names what is in the way, as data. It
//! does NOT say what to do about it: ending the old king and
//! crowning the new one somewhere else are both good answers, and
//! the crate cannot know which one the story wants.
//!
//! No prose lives here. `Display` gives a default line, and the
//! consumer words it its own way.

use crate::entity::EntityType;
use crate::fact::Direction;
use crate::time::{EntityId, Tick};
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Rejection {
    /// Wrong on its own. Checking it needs only the vocabulary.
    Malformed(Malformed),
    /// Fine on its own. It contradicts the world as it is now.
    Contradiction(Contradiction),
}

impl Rejection {
    pub fn malformed(&self) -> bool {
        matches!(self, Rejection::Malformed(_))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Malformed {
    /// The vocabulary does not hold this name.
    UnknownFact { name: String },
    /// The name takes a number, and the event carries none.
    NeedsNumber { name: String },
    /// The name takes no number, and the event carries one.
    TakesNoNumber { name: String },
    /// The name takes a second entity, and the event names none.
    NeedsTarget { name: String },
    /// The name takes no second entity, and the event names one.
    TakesNoTarget { name: String },
    /// This holder type cannot hold this name about this target
    /// type (spec decision 33).
    TypeNotAllowed {
        name: String,
        holder: EntityType,
        target: EntityType,
    },
    /// The number sits outside the band of the name.
    OutOfBand {
        name: String,
        value: i64,
        min: i64,
        max: i64,
    },
    /// The write moves against the direction of the name. An end
    /// carries no `to`, because an end is a write to nothing.
    Backward {
        name: String,
        direction: Direction,
        from: Option<i64>,
        to: Option<i64>,
    },
    /// The entity carries no name, so no reason can point at it.
    UnnamedEntity { id: EntityId },
    /// A memory record cannot merge this name, so two devices
    /// hold two answers and neither one wins.
    Unmergeable { name: String, why: Unmergeable },
    /// The vocabulary itself is wrong. A caller writes the
    /// vocabulary, so a caller can be wrong.
    BrokenVocabulary { name: String, fault: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Contradiction {
    /// No entity carries this handle.
    UnknownEntity { id: EntityId },
    /// The entity is dead. A dead entity gains no facts.
    Gone { id: EntityId },
    /// The fact points the entity at itself.
    SelfReference { id: EntityId },
    /// That puts Ashford inside itself. `through` names the
    /// entity on the chain that already sits inside `entity`.
    Cycle { entity: EntityId, through: EntityId },
    /// More entities hold this name about one target than the
    /// count allows. `held_by` names the ones in the way.
    TooManyHolders {
        name: String,
        target: EntityId,
        held_by: Vec<EntityId>,
        limit: u16,
    },
    /// One entity holds this name about more targets than the
    /// count allows. `pointing_at` names the ones in the way.
    TooManyTargets {
        name: String,
        holder: EntityId,
        pointing_at: Vec<EntityId>,
        limit: u16,
    },
    /// The handle is already in use. An id is never reused,
    /// because the history names the dead.
    IdInUse { id: EntityId },
    /// The event changes or ends a fact that does not hold.
    NoSuchFact {
        entity: EntityId,
        name: String,
        linked_to: Option<EntityId>,
    },
    /// The update read a number the world no longer holds. This
    /// is the compare-and-swap of decision 33 and a half: a
    /// director works from a briefing, and the world moved while
    /// it was thinking.
    Stale {
        entity: EntityId,
        name: String,
        want: i64,
        got: i64,
    },
    /// The write moves against the direction of the name, against
    /// what the world holds now. Starting a best depth again at
    /// zero is the case this catches.
    Backward {
        entity: EntityId,
        name: String,
        direction: Direction,
        held: Option<i64>,
        proposed: Option<i64>,
    },
    /// The tick of the event sits before the tick of the world,
    /// so the history loses its order.
    TimeMovedBack { was: Tick, got: Tick },
    /// The schema grew, and the change has no path (see
    /// `migrate`).
    NoMigrationPath { name: String, why: Migration },
    /// The version does not step by one over a schema change, or
    /// it steps over no change.
    VersionStep {
        from: u32,
        to: u32,
        schema_changed: bool,
    },
}

/// Why a memory record cannot merge one name.
///
/// A merge of two records must answer the same thing whichever
/// record comes first, and an empty record must change nothing.
/// Both hold when the join of one field starts from ABSENT.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Unmergeable {
    /// The name moves either way, so two records disagree and
    /// neither one is later.
    NoDirection,
    /// The name is a flag that only falls. An empty record then
    /// deletes it, so a device that never heard of the flag
    /// erases it on the first merge.
    VanishingFlag,
    /// The name links two entities, and a record is flat. A
    /// memory holds what a device remembers, not who it points
    /// at.
    TakesTarget,
}

/// Why a schema change has no path. A migration is additive only.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Migration {
    /// The new schema drops a name the old one declared.
    DroppedName,
    /// The rules of a declared name changed. `apply` reads the
    /// rules, so an old history folds into a new state, and the
    /// log and the state drift apart.
    RulesChanged,
    /// The band of a declared name narrowed, so a number the
    /// world already holds falls outside it.
    BandNarrowed { was: (i64, i64), now: (i64, i64) },
}

// ---------------------------------------------------------------
// The default line. The consumer writes its own.
// ---------------------------------------------------------------

impl fmt::Display for Rejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rejection::Malformed(m) => write!(f, "{m}"),
            Rejection::Contradiction(c) => write!(f, "{c}"),
        }
    }
}

impl fmt::Display for Malformed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Malformed::UnknownFact { name } => write!(f, "no fact is called {name}"),
            Malformed::NeedsNumber { name } => write!(f, "{name} takes a number"),
            Malformed::TakesNoNumber { name } => write!(f, "{name} takes no number"),
            Malformed::NeedsTarget { name } => write!(f, "{name} takes a second entity"),
            Malformed::TakesNoTarget { name } => write!(f, "{name} takes no second entity"),
            Malformed::TypeNotAllowed {
                name,
                holder,
                target,
            } => write!(
                f,
                "{name} does not go from a {} to a {}",
                holder.label(),
                target.label()
            ),
            Malformed::OutOfBand {
                name,
                value,
                min,
                max,
            } => write!(f, "{name} holds {min} to {max}, and the event says {value}"),
            Malformed::Backward {
                name,
                direction,
                from,
                to,
            } => match (from, to) {
                (Some(a), Some(b)) => write!(
                    f,
                    "{name} moves {}, and {a} to {b} does not",
                    direction.label()
                ),
                _ => write!(f, "{name} moves {}, so it never ends", direction.label()),
            },
            Malformed::UnnamedEntity { id } => write!(f, "entity {} carries no name", id.0),
            Malformed::Unmergeable { name, why } => match why {
                Unmergeable::NoDirection => {
                    write!(f, "{name} moves either way, so two records cannot merge")
                }
                Unmergeable::VanishingFlag => {
                    write!(f, "{name} is a flag that falls, so a merge would erase it")
                }
                Unmergeable::TakesTarget => {
                    write!(f, "{name} links two entities, and a record is flat")
                }
            },
            Malformed::BrokenVocabulary { name, fault } => {
                write!(f, "the rules of {name} are wrong: {fault}")
            }
        }
    }
}

impl fmt::Display for Contradiction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Contradiction::UnknownEntity { id } => write!(f, "no entity {}", id.0),
            Contradiction::Gone { id } => write!(f, "entity {} is gone", id.0),
            Contradiction::SelfReference { id } => write!(f, "entity {} points at itself", id.0),
            Contradiction::Cycle { entity, through } => write!(
                f,
                "that puts entity {} inside itself, through entity {}",
                entity.0, through.0
            ),
            Contradiction::TooManyHolders {
                name,
                target,
                held_by,
                limit,
            } => write!(
                f,
                "entity {} already holds {name} from {} of {limit}",
                target.0,
                held_by.len()
            ),
            Contradiction::TooManyTargets {
                name,
                holder,
                pointing_at,
                limit,
            } => write!(
                f,
                "entity {} already points {name} at {} of {limit}",
                holder.0,
                pointing_at.len()
            ),
            Contradiction::IdInUse { id } => write!(f, "entity {} is taken", id.0),
            Contradiction::NoSuchFact { entity, name, .. } => {
                write!(f, "entity {} does not hold {name}", entity.0)
            }
            Contradiction::Stale {
                entity,
                name,
                want,
                got,
            } => write!(
                f,
                "{name} of entity {} is {got}, and the event read {want}",
                entity.0
            ),
            Contradiction::Backward {
                entity,
                name,
                direction,
                held,
                proposed,
            } => match (held, proposed) {
                (Some(a), Some(b)) => write!(
                    f,
                    "{name} of entity {} moves {}, and {a} to {b} does not",
                    entity.0,
                    direction.label()
                ),
                _ => write!(
                    f,
                    "{name} of entity {} moves {}, so it never ends",
                    entity.0,
                    direction.label()
                ),
            },
            Contradiction::TimeMovedBack { was, got } => {
                write!(
                    f,
                    "the world is at tick {}, and the event says {}",
                    was.0, got.0
                )
            }
            Contradiction::NoMigrationPath { name, why } => match why {
                Migration::DroppedName => write!(f, "the new schema drops {name}"),
                Migration::RulesChanged => write!(f, "the rules of {name} changed"),
                Migration::BandNarrowed { was, now } => write!(
                    f,
                    "the band of {name} was {} to {}, and it is now {} to {}",
                    was.0, was.1, now.0, now.1
                ),
            },
            Contradiction::VersionStep {
                from,
                to,
                schema_changed,
            } => {
                if *schema_changed {
                    write!(f, "the schema changed, and the version went {from} to {to}")
                } else {
                    write!(f, "the schema held, and the version went {from} to {to}")
                }
            }
        }
    }
}
