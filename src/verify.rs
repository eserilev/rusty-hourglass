//! The self check: a referee, not an echo.
//!
//! `verify` reads a world and answers whether it obeys every
//! invariant of the spec. The claim is total: for every proposal,
//! `propose` refuses, or `verify` passes on the world that `propose`
//! leaves behind. The Lean theorem `every_proposed_world_verifies`
//! proves the claim for every world that proposals build.
//!
//! The check shares no code path with `apply` or with the gate. It
//! folds the history with its own writer, over its own rows, and then
//! it compares. So a bug in `apply` shows up as a disagreement
//! between two independent programs.
//!
//! The code is a set of index loops, so Aeneas translates it. Each
//! loop body with an early answer is a function of its own.
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

use crate::entity::{Entity, EntityType};
use crate::event::{Event, EventKind};
use crate::fact::{is_located_in, Count, Fact, FactRules, Shape};
use crate::ids::Ids;
use crate::time::{EntityId, EventId, Tick};
use crate::world::World;

/// One row of the referee state. A tuple, not the struct of the
/// crate, so the two folds share no shape.
type Slot = (String, Option<i64>, Option<EntityId>, EventId);

struct Row {
    kind: EntityType,
    name: String,
    from: Tick,
    until: Option<Tick>,
    slots: Vec<Slot>,
}

#[cfg_attr(charon, verify::start_from)]
pub fn verify(w: &World) -> bool {
    let rows = refold(w);
    same_state(w, &rows) && sound(w)
}

/// Fold the history again, with the other writer.
fn refold(w: &World) -> Ids<Row> {
    let evs = w.history().events();
    let mut rows = Ids::new();
    let mut i = 0;
    while i < evs.len() {
        refold_one(w, &mut rows, &evs[i]);
        i += 1;
    }
    rows
}

fn refold_one(w: &World, rows: &mut Ids<Row>, ev: &Event) {
    match &ev.kind {
        EventKind::EntityCreated {
            id,
            entity_type,
            name,
        } => {
            if !rows.contains(*id) {
                rows.insert(
                    *id,
                    Row {
                        kind: *entity_type,
                        name: name.clone(),
                        from: ev.tick,
                        until: None,
                        slots: Vec::new(),
                    },
                );
            }
        }
        EventKind::EntityDestroyed { id } => {
            if let Some(mut row) = rows.take(*id) {
                if row.until.is_none() {
                    row.until = Some(ev.tick);
                }
                rows.insert(*id, row);
            }
        }
        EventKind::FactStart {
            entity: who,
            name,
            value,
            linked_to,
        } => {
            let wide = one_target(w, name);
            if let Some(mut row) = rows.take(*who) {
                let mut kept = kept_slots(&row.slots, name, *linked_to, wide);
                kept.push((name.clone(), *value, *linked_to, ev.id));
                row.slots = kept;
                rows.insert(*who, row);
            }
        }
        EventKind::FactUpdate {
            entity: who,
            name,
            linked_to,
            to,
            ..
        } => {
            if let Some(mut row) = rows.take(*who) {
                let mut j = 0;
                while j < row.slots.len() {
                    update_slot(&mut row.slots[j], name, *linked_to, *to, ev.id);
                    j += 1;
                }
                rows.insert(*who, row);
            }
        }
        EventKind::FactEnd {
            entity: who,
            name,
            linked_to,
        } => {
            if let Some(mut row) = rows.take(*who) {
                row.slots = kept_slots(&row.slots, name, *linked_to, false);
                rows.insert(*who, row);
            }
        }
    }
}

/// The slots that a start or an end keeps. A wide name clears every
/// slot of the name, and a narrow one clears its own slot.
#[allow(clippy::ptr_arg)]
fn kept_slots(
    slots: &[Slot],
    name: &String,
    linked_to: Option<EntityId>,
    wide: bool,
) -> Vec<Slot> {
    let mut kept = Vec::new();
    let mut i = 0;
    while i < slots.len() {
        keep_slot(&mut kept, &slots[i], name, linked_to, wide);
        i += 1;
    }
    kept
}

#[allow(clippy::ptr_arg)]
fn keep_slot(
    kept: &mut Vec<Slot>,
    slot: &Slot,
    name: &String,
    linked_to: Option<EntityId>,
    wide: bool,
) {
    let clash = if wide {
        slot.0 == *name
    } else {
        slot.0 == *name && slot.2 == linked_to
    };
    if !clash {
        kept.push((slot.0.clone(), slot.1, slot.2, slot.3));
    }
}

#[allow(clippy::ptr_arg)]
fn update_slot(slot: &mut Slot, name: &String, linked_to: Option<EntityId>, to: i64, id: EventId) {
    if slot.0 == *name && slot.2 == linked_to {
        slot.1 = Some(to);
        slot.3 = id;
    }
}

/// Does one name allow one target at a time? Written again, from
/// the vocabulary alone.
#[allow(clippy::ptr_arg)]
fn one_target(w: &World, name: &String) -> bool {
    match w.vocabulary.rules_key(name) {
        Some(FactRules::Linked { targets, .. }) => targets.limit() == Some(1),
        _ => false,
    }
}

/// Invariant 1. The state is the fold of the history.
fn same_state(w: &World, rows: &Ids<Row>) -> bool {
    if w.len() != rows.len() {
        return false;
    }
    let ids = w.entity_ids();
    let mut i = 0;
    while i < ids.len() {
        if !same_row(w, rows, ids[i]) {
            return false;
        }
        i += 1;
    }
    ticks_rise(w)
}

fn same_row(w: &World, rows: &Ids<Row>, key: EntityId) -> bool {
    let Some(e) = w.entity(key) else {
        return false;
    };
    let Some(row) = rows.get(e.id) else {
        return false;
    };
    if row.kind != e.entity_type || row.name != e.name {
        return false;
    }
    if row.from != e.existence.from || row.until != e.existence.until {
        return false;
    }
    if row.slots.len() != e.facts.len() {
        return false;
    }
    let mut i = 0;
    while i < row.slots.len() {
        if !same_slot(&row.slots[i], &e.facts[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn same_slot(slot: &Slot, f: &Fact) -> bool {
    slot.0 == f.name && slot.1 == f.value && slot.2 == f.linked_to && slot.3 == f.opened
}

/// Invariant 12, and the tick of the world.
fn ticks_rise(w: &World) -> bool {
    let evs = w.history().events();
    let mut last = Tick(0);
    let mut i = 0;
    while i < evs.len() {
        if evs[i].tick < last {
            return false;
        }
        last = evs[i].tick;
        i += 1;
    }
    w.tick >= last
}

/// Invariants 2 to 11.
fn sound(w: &World) -> bool {
    // Invariant 11.
    let mut created: Ids<()> = Ids::new();
    if !all_created_once(w, &mut created) {
        return false;
    }
    all_entities_sound(w, &created)
}

fn all_created_once(w: &World, created: &mut Ids<()>) -> bool {
    let evs = w.history().events();
    let mut i = 0;
    while i < evs.len() {
        if !created_once(w, created, &evs[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn all_entities_sound(w: &World, created: &Ids<()>) -> bool {
    let ids = w.entity_ids();
    let mut k = 0;
    while k < ids.len() {
        if !entity_sound(w, created, ids[k]) {
            return false;
        }
        k += 1;
    }
    true
}

/// A second creation of a live entity lets one handle name two
/// things.
fn created_once(w: &World, created: &mut Ids<()>, ev: &Event) -> bool {
    if let EventKind::EntityCreated { id, .. } = &ev.kind {
        if created.contains(*id) && w.entity(*id).is_some() {
            return false;
        }
        created.insert(*id, ());
    }
    true
}

fn entity_sound(w: &World, created: &Ids<()>, key: EntityId) -> bool {
    let Some(e) = w.entity(key) else {
        return false;
    };
    if !created.contains(e.id) {
        return false;
    }
    // Invariant 5.
    if !e.existence.sound() {
        return false;
    }
    let mut i = 0;
    while i < e.facts.len() {
        if !fact_sound(w, e, i) {
            return false;
        }
        i += 1;
    }
    // Invariant 8.
    walk_is_finite(w, e.id)
}

fn fact_sound(w: &World, e: &Entity, i: usize) -> bool {
    let f = &e.facts[i];
    // Invariant 2.
    let Some(rules) = w.vocabulary.rules_key(&f.name) else {
        return false;
    };
    // Invariant 3.
    !slot_before(&e.facts, i)
        // Invariant 4.
        && opened_inside(w, f)
        // Invariant 10.
        && value_fits(rules, f)
        // Invariant 9.
        && link_fits(w, e, rules, f)
        // Invariants 6 and 7.
        && counts_hold(w, e, rules, f)
}

fn opened_inside(w: &World, f: &Fact) -> bool {
    (f.opened.0 as usize) < w.history().len()
}

fn value_fits(rules: &FactRules, f: &Fact) -> bool {
    match (rules.shape(), f.value) {
        (Shape::Number { band, .. }, Some(n)) => band.holds(n),
        (Shape::Number { .. }, None) => false,
        (Shape::Flag { .. }, Some(_)) => false,
        (Shape::Flag { .. }, None) => true,
    }
}

fn link_fits(w: &World, e: &Entity, rules: &FactRules, f: &Fact) -> bool {
    match (rules.takes_target(), f.linked_to) {
        (true, None) => false,
        (false, Some(_)) => false,
        (true, Some(target)) => {
            if target == e.id {
                return false;
            }
            let Some(other) = w.type_of(target) else {
                return false;
            };
            rules.type_allowed(e.entity_type, other)
        }
        (false, None) => true,
    }
}

fn counts_hold(w: &World, e: &Entity, rules: &FactRules, f: &Fact) -> bool {
    let FactRules::Linked {
        holders, targets, ..
    } = rules
    else {
        return true;
    };
    holders_fit(w, *holders, f) && targets_fit(e, *targets, f)
}

fn holders_fit(w: &World, holders: Count, f: &Fact) -> bool {
    match (holders.limit(), f.linked_to) {
        (Some(limit), Some(target)) => holders_count(w, &f.name, target) <= usize::from(limit),
        _ => true,
    }
}

fn targets_fit(e: &Entity, targets: Count, f: &Fact) -> bool {
    match targets.limit() {
        Some(limit) => distinct_targets(&e.facts, &f.name) <= usize::from(limit),
        None => true,
    }
}

/// Does a fact before `i` sit in the slot of the fact at `i`?
fn slot_before(facts: &[Fact], i: usize) -> bool {
    let mut j = 0;
    while j < i {
        if facts[j].name == facts[i].name && facts[j].linked_to == facts[i].linked_to {
            return true;
        }
        j += 1;
    }
    false
}

/// The number of entities that hold the name about the target.
#[allow(clippy::ptr_arg)]
fn holders_count(w: &World, name: &String, target: EntityId) -> usize {
    let ids = w.entity_ids();
    let mut n = 0;
    let mut i = 0;
    while i < ids.len() {
        if holds_slot(w, ids[i], name, target) {
            n += 1;
        }
        i += 1;
    }
    n
}

#[allow(clippy::ptr_arg)]
fn holds_slot(w: &World, key: EntityId, name: &String, target: EntityId) -> bool {
    let Some(e) = w.entity(key) else {
        return false;
    };
    let mut i = 0;
    while i < e.facts.len() {
        if e.facts[i].name == *name && e.facts[i].linked_to == Some(target) {
            return true;
        }
        i += 1;
    }
    false
}

/// The number of different targets among the facts of the name.
#[allow(clippy::ptr_arg)]
fn distinct_targets(facts: &[Fact], name: &String) -> usize {
    let mut n = 0;
    let mut i = 0;
    while i < facts.len() {
        if first_target(facts, name, i) {
            n += 1;
        }
        i += 1;
    }
    n
}

/// Is the fact at `i` the first fact of the name with its target?
#[allow(clippy::ptr_arg)]
fn first_target(facts: &[Fact], name: &String, i: usize) -> bool {
    if facts[i].name != *name || facts[i].linked_to.is_none() {
        return false;
    }
    let mut j = 0;
    while j < i {
        if facts[j].name == *name && facts[j].linked_to == facts[i].linked_to {
            return false;
        }
        j += 1;
    }
    true
}

/// Invariant 8. The walk up the chain from the entity ends. Each
/// stop with a place is an entity of the world, so a chain with no
/// ring ends within `len` hops. A chain still going after `len` hops
/// meets a ring.
fn walk_is_finite(w: &World, start: EntityId) -> bool {
    let n = w.len();
    let mut at = start;
    let mut hops = 0;
    while hops < n {
        match up(w, at) {
            None => return true,
            Some(next) => at = next,
        }
        hops += 1;
    }
    up(w, at).is_none()
}

/// The place of the entity: the target of its first `located_in`
/// fact, with its own loop.
#[allow(clippy::question_mark)]
fn up(w: &World, at: EntityId) -> Option<EntityId> {
    let Some(row) = w.entity(at) else {
        return None;
    };
    let mut i = 0;
    while i < row.facts.len() {
        if is_located_in(&row.facts[i].name) {
            return row.facts[i].linked_to;
        }
        i += 1;
    }
    None
}
