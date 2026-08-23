//! The handles and the clock (spec decisions 5, 6, and 17).
//!
//! Four small types. Three are whole numbers with a name, and the
//! fourth is a stretch of time. Nothing here reads a system
//! clock: every tick arrives on an event, so a replay of one
//! history builds one state on any machine.

use serde::{Deserialize, Serialize};

/// A handle on one entity. Never reused, because the history
/// names the dead (spec decision 31).
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Default,
)]
#[serde(transparent)]
pub struct EntityId(pub u32);

/// The position of one event in the history.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Default,
)]
#[serde(transparent)]
pub struct EventId(pub u64);

/// One step of world time. A tick is not a frame. It is as long
/// as the game says: an hour, a day, or a season.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Default,
)]
#[serde(transparent)]
pub struct Tick(pub u64);

/// A stretch of time that started and maybe ended.
///
/// The span holds its start and not its end. An entity that dies
/// at tick 50 is alive at 49 and gone at 50. One rule, and no
/// argument about the edge.
///
/// Only [`crate::Entity::existence`] uses it. A fact leaves the
/// state when it ends, so a fact needs no span (spec decision 15).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TimeSpan {
    pub from: Tick,
    pub until: Option<Tick>,
}

impl TimeSpan {
    /// A span that started and has not ended.
    pub fn open(from: Tick) -> Self {
        TimeSpan { from, until: None }
    }

    /// A span that started and ended.
    pub fn closed(from: Tick, until: Tick) -> Self {
        TimeSpan {
            from,
            until: Some(until),
        }
    }

    /// Was this true at that tick?
    pub fn holds_at(&self, at: Tick) -> bool {
        if at < self.from {
            return false;
        }
        match self.until {
            None => true,
            Some(end) => at < end,
        }
    }

    /// Has the span ended?
    pub fn ended(&self) -> bool {
        self.until.is_some()
    }

    /// A span never ends before it starts.
    pub fn sound(&self) -> bool {
        match self.until {
            None => true,
            Some(end) => end >= self.from,
        }
    }
}
