//! The memory of a run: what one device remembers between runs.
//!
//! The named consumer is the roguelike of Sandcastle. A kid dives
//! to floor 7, dies, and starts again. The best depth, the
//! unlocks earned, and the meta progression must survive the run.
//! The platform already carries that record: `Game.progress`
//! writes the player scope, and its save takes the BIGGER of the
//! old number and the new one.
//!
//! This module is that record with a schema and a proof.
//!
//! # A record is the flat cut of one entity
//!
//! A [`Record`] is a flat map of a name to a whole number or a
//! flag. It is the solo facts of one entity, and nothing else.
//! The JSON shape is the JSON shape the platform already stores,
//! so a server reads a record straight from the player scope.
//!
//! # Absence is the start of every join
//!
//! Two devices hold two records, and the merge must answer the
//! same thing whichever record comes first. It must answer the
//! same thing whether the merge runs once or twice. And an empty
//! record must change nothing.
//!
//! All three hold when the join of one field starts from ABSENT:
//!
//! | shape and direction | the join | absent means |
//! |---|---|---|
//! | number, up | the larger | nothing recorded yet |
//! | number, down | the smaller | nothing recorded yet |
//! | flag, up | either one | not earned yet |
//!
//! Every other declaration is refused, and each one breaks a law:
//! a free field has no later answer, a device that never heard
//! of a falling flag erases it, and a linked name has no place in
//! a flat record.
//!
//! That is why this crate never needs a DEFAULT for a new field.
//! Clepsydra makes a migration carry one, because a row that
//! misses a key reads `undefined`. Here a missing key IS the
//! start value, so a schema grows with nothing to fill in.

use crate::event::EventKind;
use crate::fact::{Direction, FactRules, FactVocabulary, Shape};
use crate::reject::{Malformed, Rejection, Unmergeable};
use crate::time::EntityId;
use crate::world::World;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

/// One value in a record. A whole number, or a flag.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Value {
    Flag(bool),
    Number(i64),
}

impl Value {
    /// Does this value say anything? A flag that is false says
    /// the same as a name the record never carried.
    pub fn present(&self) -> bool {
        !matches!(self, Value::Flag(false))
    }

    pub fn number(&self) -> Option<i64> {
        match self {
            Value::Number(n) => Some(*n),
            Value::Flag(_) => None,
        }
    }
}

/// What one device remembers between runs.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Record(BTreeMap<String, Value>);

impl Record {
    pub fn new() -> Self {
        Record(BTreeMap::new())
    }

    pub fn get(&self, name: &str) -> Option<Value> {
        self.0.get(name).copied().filter(|v| v.present())
    }

    pub fn number(&self, name: &str) -> Option<i64> {
        self.get(name).and_then(|v| v.number())
    }

    pub fn flag(&self, name: &str) -> bool {
        matches!(self.get(name), Some(Value::Flag(true)))
    }

    /// Write one value. A flag that is false leaves the record,
    /// so one record has one shape.
    pub fn set(&mut self, name: &str, value: Value) -> &mut Self {
        if value.present() {
            self.0.insert(name.to_string(), value);
        } else {
            self.0.remove(name);
        }
        self
    }

    pub fn with(mut self, name: &str, value: Value) -> Self {
        self.set(name, value);
        self
    }

    pub fn names(&self) -> impl Iterator<Item = (&String, &Value)> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// How one name joins two records.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Join {
    /// The larger number wins.
    Larger,
    /// The smaller number wins.
    Smaller,
    /// The flag wins over the empty.
    Either,
}

impl Join {
    /// The join of two values. Both arrive present.
    pub fn of(&self, a: Value, b: Value) -> Value {
        match (self, a, b) {
            (Join::Larger, Value::Number(x), Value::Number(y)) => Value::Number(x.max(y)),
            (Join::Smaller, Value::Number(x), Value::Number(y)) => Value::Number(x.min(y)),
            (Join::Either, _, _) => Value::Flag(true),
            // A record that passed `check` never reaches here.
            // The join of two shapes that do not match keeps the
            // first, so the function stays total.
            _ => a,
        }
    }
}

/// Can this name live in a memory record, and how does it join?
pub fn join_of(rules: &FactRules) -> Result<Join, Unmergeable> {
    if rules.takes_target() {
        return Err(Unmergeable::TakesTarget);
    }
    match rules.shape() {
        Shape::Number {
            direction: Direction::Up,
            ..
        } => Ok(Join::Larger),
        Shape::Number {
            direction: Direction::Down,
            ..
        } => Ok(Join::Smaller),
        Shape::Flag {
            direction: Direction::Up,
        } => Ok(Join::Either),
        Shape::Flag {
            direction: Direction::Down,
        } => Err(Unmergeable::VanishingFlag),
        _ => Err(Unmergeable::NoDirection),
    }
}

/// Every name of the schema a record can carry.
pub fn memory_names(schema: &FactVocabulary) -> Vec<String> {
    schema
        .names()
        .filter(|(_, rules)| join_of(rules).is_ok())
        .map(|(name, _)| name.clone())
        .collect()
}

/// Does this record fit the schema? Every reason comes back at
/// once.
///
/// Three faults: a name the schema never declared, a value of the
/// wrong shape, and a number outside its band.
pub fn check(schema: &FactVocabulary, record: &Record) -> Vec<Rejection> {
    let mut out = Vec::new();
    for (name, value) in record.names() {
        let Some(rules) = schema.rules(name) else {
            out.push(Rejection::Malformed(Malformed::UnknownFact {
                name: name.clone(),
            }));
            continue;
        };
        if let Err(why) = join_of(rules) {
            out.push(Rejection::Malformed(Malformed::Unmergeable {
                name: name.clone(),
                why,
            }));
            continue;
        }
        match (rules.shape(), value) {
            (Shape::Number { band, .. }, Value::Number(n)) => {
                if !band.holds(*n) {
                    out.push(Rejection::Malformed(Malformed::OutOfBand {
                        name: name.clone(),
                        value: *n,
                        min: band.min,
                        max: band.max,
                    }));
                }
            }
            (Shape::Number { .. }, Value::Flag(_)) => {
                out.push(Rejection::Malformed(Malformed::NeedsNumber {
                    name: name.clone(),
                }))
            }
            (Shape::Flag { .. }, Value::Number(_)) => {
                out.push(Rejection::Malformed(Malformed::TakesNoNumber {
                    name: name.clone(),
                }))
            }
            (Shape::Flag { .. }, Value::Flag(_)) => {}
        }
    }
    out
}

/// Merge two records. The answer is the same whichever record
/// comes first, the same however the merges group, and the same
/// however many times it runs.
///
/// Every reason a record does not fit the schema comes back at
/// once, and nothing merges until both records fit.
pub fn merge(schema: &FactVocabulary, a: &Record, b: &Record) -> Result<Record, Vec<Rejection>> {
    let mut faults = check(schema, a);
    faults.extend(check(schema, b));
    if !faults.is_empty() {
        return Err(faults);
    }
    let mut names: BTreeSet<&String> = BTreeSet::new();
    names.extend(a.0.keys());
    names.extend(b.0.keys());
    let mut out = Record::new();
    for name in names {
        let Some(rules) = schema.rules(name) else {
            continue;
        };
        let Ok(join) = join_of(rules) else {
            continue;
        };
        let got = match (a.get(name), b.get(name)) {
            (Some(x), Some(y)) => join.of(x, y),
            // Absent is the start of the join, so one side alone
            // wins. No default, and no clamp.
            (Some(x), None) => x,
            (None, Some(y)) => y,
            (None, None) => continue,
        };
        out.set(name, got);
    }
    Ok(out)
}

/// The flat cut of one entity: its solo facts, as a record.
pub fn record(world: &World, entity: EntityId) -> Record {
    let mut out = Record::new();
    let Some(row) = world.entity(entity) else {
        return out;
    };
    for fact in &row.facts {
        if fact.linked_to.is_some() {
            continue;
        }
        match fact.value {
            Some(n) => out.set(&fact.name, Value::Number(n)),
            None => out.set(&fact.name, Value::Flag(true)),
        };
    }
    out
}

/// The events that bring one entity up to this record.
///
/// A write only moves forward, so the list holds a start and a
/// change and never an end. A name the world already matches
/// writes nothing.
///
/// The list goes through `propose`, so the gate is the same gate.
/// This function guesses no rule of its own.
pub fn writes(world: &World, entity: EntityId, want: &Record) -> Vec<EventKind> {
    let mut out = Vec::new();
    for (name, value) in want.names() {
        if !value.present() {
            continue;
        }
        let held = world.entity(entity).and_then(|e| e.fact(name, None));
        match (held, value) {
            (None, Value::Number(n)) => out.push(EventKind::FactStart {
                entity,
                name: name.clone(),
                value: Some(*n),
                linked_to: None,
            }),
            (None, Value::Flag(_)) => out.push(EventKind::FactStart {
                entity,
                name: name.clone(),
                value: None,
                linked_to: None,
            }),
            (Some(fact), Value::Number(n)) => {
                if fact.value != Some(*n) {
                    out.push(EventKind::FactUpdate {
                        entity,
                        name: name.clone(),
                        linked_to: None,
                        from: fact.value.unwrap_or(*n),
                        to: *n,
                    });
                }
            }
            (Some(_), Value::Flag(_)) => {}
        }
    }
    out
}
