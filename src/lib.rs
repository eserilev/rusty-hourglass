//! Hourglass: a world that remembers (SPEC.md).
//!
//! A world holds entities: people, places, things, and factions.
//! Facts change that world over time, and the changes are
//! permanent. A king dies and stays dead. A house burns, and the
//! history keeps the fire even after somebody rebuilds it.
//!
//! Hourglass is the world and its rules. It is NOT the
//! storyteller. A director sits outside, asks a model what
//! happens next, and proposes it. Hourglass says yes or no, and
//! remembers.
//!
//! # The shape
//!
//! ```text
//! EventHistory                     the truth. append-only, ordered.
//!    |
//!    |  apply, one event at a time
//!    v
//! state   entities, each with facts  derived.
//!    |
//!    |  brief
//!    v
//! Briefing                          what the director reads.
//! ```
//!
//! Both halves feed the prompt. "How things are now" comes from
//! the state. "What just happened" comes from the tail of the
//! history. A history with no state means a full replay on every
//! prompt. A state with no history loses why anything happened.
//!
//! # The four promises
//!
//! 1. **The same events always give the same state.** No
//!    unordered collection, no float, no system clock, no
//!    unseeded random source, and nothing outside the two
//!    arguments of `apply`.
//! 2. **A refusal carries every reason at once**, so one retry
//!    fixes everything.
//! 3. **Each event stands alone.** The good ones land, and only
//!    the bad ones come back. A bad proposal costs one event,
//!    never the whole tick.
//! 4. **Rollback is cheap.** Cut the history and replay it. That
//!    costs nothing, because `apply` builds the state from
//!    nothing, and it IS the undo of a child.
//!
//! # The vocabulary is caller data
//!
//! [`FactVocabulary`] maps a name to its rules: a flag or a
//! number, the band, the direction, how many links each side
//! allows, and which entity types. The crate holds no product
//! word, so a world of a game server and the memory of a
//! roguelike compile through the same code. The same list goes
//! into a director prompt, so a closed set goes in and a closed
//! set comes out ([`FactVocabulary::describe`]).
//!
//! The crate declares one name itself: `located_in`. A consumer
//! never types it, and never misspells it.
//!
//! # The memory of a run
//!
//! [`Record`] is the first consumer: what one device remembers
//! between runs. A best depth that never falls, unlocks that are
//! never lost, and a merge of two devices ([`merge`]). The Kani
//! harnesses prove the join laws per value: the larger number,
//! the band, the direction, the count, and the span. `merge`
//! applies that join name by name. Lean theorems prove the three
//! record laws for every record (same either way, same grouping,
//! self-merge is identity). The seeded sweep in `tests/laws.rs`
//! checks them a second time against a naive oracle. See the
//! [`memory`] module and `lean/README.md`.
//!
//! # Whole numbers, everywhere
//!
//! No float enters the crate. Every law states as a theorem a
//! solver can read.

// Charon reads the `verify::start_from` marks when it translates the
// crate to Lean (lean/extract.sh). The tool and the marks exist only
// under `--cfg charon`, so a normal build never sees them.
#![cfg_attr(charon, feature(register_tool), register_tool(verify))]

mod brief;
mod entity;
mod event;
mod fact;
mod ids;
mod memory;
mod migrate;
mod names;
mod reject;
mod time;
mod validate;
mod verify;
mod world;

#[cfg(kani)]
mod proofs;

pub use brief::{brief, Briefing, Budget};
pub use entity::{Entity, EntityType};
pub use event::{Event, EventHistory, EventKind};
pub use fact::{
    located_in_rules, Band, Count, Direction, Fact, FactLine, FactRules, FactVocabulary, Shape,
    LOCATED_IN,
};
pub use memory::{check, join_of, memory_names, merge, record, writes, Join, Record, Value};
pub use migrate::{migrate, schema_changed, upgrade};
pub use reject::{Contradiction, Malformed, Migration, Rejection, Unmergeable};
pub use time::{EntityId, EventId, Tick, TimeSpan};
pub use validate::{validate, vocabulary_sound};
pub use verify::verify;
pub use world::{World, MAX_HOPS};
