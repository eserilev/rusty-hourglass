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
use crate::names::Names;
use crate::reject::{Malformed, Rejection, Unmergeable};
use crate::time::EntityId;
use crate::world::World;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

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
    #[cfg_attr(charon, verify::start_from)]
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
///
/// One record has one shape: a flag that is false never sits in
/// the map. `set` keeps that on write, and the read from JSON
/// keeps it on the way in, so a record from the platform store and
/// the same record built in code are equal, and `merge(r, r) == r`
/// holds for every input.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(from = "BTreeMap<String, Value>", into = "BTreeMap<String, Value>")]
pub struct Record(Names<Value>);

impl From<BTreeMap<String, Value>> for Record {
    fn from(map: BTreeMap<String, Value>) -> Self {
        Record(Names::from_map(
            map.into_iter().filter(|(_, v)| v.present()).collect(),
        ))
    }
}

impl From<Record> for BTreeMap<String, Value> {
    fn from(record: Record) -> Self {
        record.0.into_map()
    }
}

impl Record {
    pub fn new() -> Self {
        Record(Names::new())
    }

    /// `get`, for the verified code (see `names.rs`).
    #[allow(clippy::ptr_arg)]
    fn value(&self, name: &String) -> Option<Value> {
        match self.0.get_key(name) {
            Some(v) => {
                if v.present() {
                    Some(*v)
                } else {
                    None
                }
            }
            None => None,
        }
    }

    /// `set`, for the verified code (see `names.rs`).
    #[allow(clippy::ptr_arg)]
    fn put(&mut self, name: &String, value: Value) {
        if value.present() {
            self.0.insert(name.clone(), value);
        } else {
            self.0.remove_key(name);
        }
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
    #[cfg_attr(charon, verify::start_from)]
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
#[cfg_attr(charon, verify::start_from)]
pub fn check(schema: &FactVocabulary, record: &Record) -> Vec<Rejection> {
    let mut out = Vec::new();
    check_into(schema, record, &mut out);
    out
}

/// `check`, with the reasons added to `out`.
fn check_into(schema: &FactVocabulary, record: &Record, out: &mut Vec<Rejection>) {
    let names = record.0.keys();
    let mut i = 0;
    while i < names.len() {
        check_name(schema, record, &names[i], out);
        i += 1;
    }
}

/// The faults of one name of the record.
#[allow(clippy::ptr_arg)]
fn check_name(schema: &FactVocabulary, record: &Record, name: &String, out: &mut Vec<Rejection>) {
    let Some(value) = record.0.get_key(name) else {
        return;
    };
    let Some(rules) = schema.rules_key(name) else {
        out.push(Rejection::Malformed(Malformed::UnknownFact {
            name: name.clone(),
        }));
        return;
    };
    if let Err(why) = join_of(rules) {
        out.push(Rejection::Malformed(Malformed::Unmergeable {
            name: name.clone(),
            why,
        }));
        return;
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

/// Merge two records. The answer is the same whichever record
/// comes first, the same however the merges group, and the same
/// however many times it runs.
///
/// Every reason a record does not fit the schema comes back at
/// once, and nothing merges until both records fit.
#[cfg_attr(charon, verify::start_from)]
pub fn merge(schema: &FactVocabulary, a: &Record, b: &Record) -> Result<Record, Vec<Rejection>> {
    let mut faults = Vec::new();
    check_into(schema, a, &mut faults);
    check_into(schema, b, &mut faults);
    if !faults.is_empty() {
        return Err(faults);
    }
    let mut out = Record::new();
    merge_names(schema, a, b, &a.0.keys(), &mut out);
    merge_names(schema, a, b, &b.0.keys(), &mut out);
    Ok(out)
}

/// Join each name of the list into `out`. A name of both records
/// comes twice, and the second write equals the first.
fn merge_names(schema: &FactVocabulary, a: &Record, b: &Record, names: &[String], out: &mut Record) {
    let mut i = 0;
    while i < names.len() {
        merge_name(schema, a, b, &names[i], out);
        i += 1;
    }
}

/// Join one name of the two records into `out`.
#[allow(clippy::ptr_arg)]
fn merge_name(schema: &FactVocabulary, a: &Record, b: &Record, name: &String, out: &mut Record) {
    let Some(rules) = schema.rules_key(name) else {
        return;
    };
    let Ok(join) = join_of(rules) else {
        return;
    };
    let got = match (a.value(name), b.value(name)) {
        (Some(x), Some(y)) => join.of(x, y),
        // Absent is the start of the join, so one side alone
        // wins. No default, and no clamp.
        (Some(x), None) => x,
        (None, Some(y)) => y,
        (None, None) => return,
    };
    out.put(name, got);
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
