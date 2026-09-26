//! The self check: a referee, not an echo.
//!
//! `verify` reads a world and answers whether it obeys every
//! invariant of the spec. The claim the tests make is total: for
//! every proposal, `propose` refuses, or `verify` passes on the
//! world that `propose` leaves behind.
//!
//! The check shares no code path with `apply`. It folds the
//! history with its own writer, over its own rows, and then it
//! compares. So a bug in `apply` shows up as a disagreement
//! between two independent programs.
//!
//! The invariants, from the spec:
//!
//! 1. The state equals the fold of the history.
//! 2. Every fact name is in the vocabulary.
//! 3. One open fact per slot.
//! 4. Every `opened` points inside the history.
//! 5. A span never ends before it starts.
//! 6. No target has more holders than its count allows.
//! 7. No holder has more targets than its count allows.
//! 8. The `located_in` graph has no ring.
//! 9. Every link obeys the type map, and both ends exist.
//! 10. Every number sits inside its band, and no flag carries one.
//! 11. Every entity in the state has exactly one creation event.
//! 12. The ticks of the history never fall.

use crate::entity::EntityType;
use crate::event::EventKind;
use crate::fact::{FactRules, Shape, LOCATED_IN};
use crate::time::{EntityId, EventId, Tick};
use crate::world::World;
use std::collections::{BTreeMap, BTreeSet};

/// One row of the referee state. A tuple list, not the struct of
/// the crate, so the two folds share no shape.
type Slot = (String, Option<i64>, Option<EntityId>, EventId);

struct Row {
    kind: EntityType,
    name: String,
    from: Tick,
    until: Option<Tick>,
    slots: Vec<Slot>,
}

pub fn verify(world: &World) -> bool {
    let rows = refold(world);
    same_state(world, &rows) && sound(world)
}

/// Fold the history again, with the other writer.
fn refold(world: &World) -> BTreeMap<EntityId, Row> {
    let mut rows: BTreeMap<EntityId, Row> = BTreeMap::new();
    for event in world.history().iter() {
        match &event.kind {
            EventKind::EntityCreated {
                id,
                entity_type,
                name,
            } => {
                if !rows.contains_key(id) {
                    rows.insert(
                        *id,
                        Row {
                            kind: *entity_type,
                            name: name.clone(),
                            from: event.tick,
                            until: None,
                            slots: Vec::new(),
                        },
                    );
                }
            }
            EventKind::EntityDestroyed { id } => {
                if let Some(row) = rows.get_mut(id) {
                    if row.until.is_none() {
                        row.until = Some(event.tick);
                    }
                }
            }
            EventKind::FactStart {
                entity,
                name,
                value,
                linked_to,
            } => {
                let wide = one_target(world, name);
                if let Some(row) = rows.get_mut(entity) {
                    let mut kept: Vec<Slot> = Vec::new();
                    for slot in row.slots.drain(..) {
                        let clash = if wide {
                            slot.0 == *name
                        } else {
                            slot.0 == *name && slot.2 == *linked_to
                        };
                        if !clash {
                            kept.push(slot);
                        }
                    }
                    kept.push((name.clone(), *value, *linked_to, event.id));
                    row.slots = kept;
                }
            }
            EventKind::FactUpdate {
                entity,
                name,
                linked_to,
                to,
                ..
            } => {
                if let Some(row) = rows.get_mut(entity) {
                    for slot in row.slots.iter_mut() {
                        if slot.0 == *name && slot.2 == *linked_to {
                            slot.1 = Some(*to);
                            slot.3 = event.id;
                        }
                    }
                }
            }
            EventKind::FactEnd {
                entity,
                name,
                linked_to,
            } => {
                if let Some(row) = rows.get_mut(entity) {
                    row.slots
                        .retain(|slot| !(slot.0 == *name && slot.2 == *linked_to));
                }
            }
        }
    }
    rows
}

/// Does one name allow one target at a time? Written again, from
/// the vocabulary alone.
fn one_target(world: &World, name: &str) -> bool {
    match world.vocabulary.rules(name) {
        Some(FactRules::Linked { targets, .. }) => targets.limit() == Some(1),
        _ => false,
    }
}

/// Invariant 1. The state is the fold of the history.
fn same_state(world: &World, rows: &BTreeMap<EntityId, Row>) -> bool {
    if world.len() != rows.len() {
        return false;
    }
    for entity in world.entities() {
        let Some(row) = rows.get(&entity.id) else {
            return false;
        };
        if row.kind != entity.entity_type || row.name != entity.name {
            return false;
        }
        if row.from != entity.existence.from || row.until != entity.existence.until {
            return false;
        }
        if row.slots.len() != entity.facts.len() {
            return false;
        }
        for (slot, fact) in row.slots.iter().zip(entity.facts.iter()) {
            if slot.0 != fact.name
                || slot.1 != fact.value
                || slot.2 != fact.linked_to
                || slot.3 != fact.opened
            {
                return false;
            }
        }
    }
    // Invariant 12, and the tick of the world.
    let mut last = Tick(0);
    for event in world.history().iter() {
        if event.tick < last {
            return false;
        }
        last = event.tick;
    }
    world.tick >= last
}

/// Invariants 2 to 11.
fn sound(world: &World) -> bool {
    let history = world.history();
    // Invariant 11.
    let mut created: BTreeSet<EntityId> = BTreeSet::new();
    for event in history.iter() {
        if let EventKind::EntityCreated { id, .. } = &event.kind {
            if !created.insert(*id) && world.entity(*id).is_some() {
                // A second creation of a live entity lets one
                // handle name two things.
                return false;
            }
        }
    }
    for entity in world.entities() {
        if !created.contains(&entity.id) {
            return false;
        }
        // Invariant 5.
        if !entity.existence.sound() {
            return false;
        }
        let mut seen: BTreeSet<(&str, Option<EntityId>)> = BTreeSet::new();
        for fact in &entity.facts {
            // Invariant 2.
            let Some(rules) = world.vocabulary.rules(&fact.name) else {
                return false;
            };
            // Invariant 3.
            if !seen.insert((fact.name.as_str(), fact.linked_to)) {
                return false;
            }
            // Invariant 4.
            if fact.opened.0 as usize >= history.len() {
                return false;
            }
            // Invariant 10.
            match (rules.shape(), fact.value) {
                (Shape::Number { band, .. }, Some(n)) => {
                    if !band.holds(n) {
                        return false;
                    }
                }
                (Shape::Number { .. }, None) => return false,
                (Shape::Flag { .. }, Some(_)) => return false,
                (Shape::Flag { .. }, None) => {}
            }
            // Invariant 9.
            match (rules.takes_target(), fact.linked_to) {
                (true, None) => return false,
                (false, Some(_)) => return false,
                (true, Some(target)) => {
                    if target == entity.id {
                        return false;
                    }
                    let Some(other) = world.type_of(target) else {
                        return false;
                    };
                    if !rules.type_allowed(entity.entity_type, other) {
                        return false;
                    }
                }
                (false, None) => {}
            }
            // Invariants 6 and 7.
            if let FactRules::Linked {
                holders, targets, ..
            } = rules
            {
                if let (Some(limit), Some(target)) = (holders.limit(), fact.linked_to) {
                    if world.holders_of(&fact.name, target).len() > usize::from(limit) {
                        return false;
                    }
                }
                if let Some(limit) = targets.limit() {
                    let mut at: BTreeSet<EntityId> = BTreeSet::new();
                    for other in entity.facts.iter().filter(|f| f.name == fact.name) {
                        if let Some(id) = other.linked_to {
                            at.insert(id);
                        }
                    }
                    if at.len() > usize::from(limit) {
                        return false;
                    }
                }
            }
        }
        // Invariant 8.
        if !walk_is_finite(world, entity.id) {
            return false;
        }
    }
    true
}

/// Invariant 8, walked with its own visited set. The set stops the
/// walk, so a long chain walks to its end.
fn walk_is_finite(world: &World, start: EntityId) -> bool {
    let mut seen: BTreeSet<EntityId> = BTreeSet::new();
    seen.insert(start);
    let mut at = start;
    loop {
        let Some(row) = world.entity(at) else {
            return true;
        };
        let Some(up) = row.facts.iter().find(|f| f.name == LOCATED_IN) else {
            return true;
        };
        let Some(next) = up.linked_to else {
            return true;
        };
        if !seen.insert(next) {
            return false;
        }
        at = next;
    }
}
