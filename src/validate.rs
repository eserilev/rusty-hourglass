//! The gate (spec decisions 35 to 39).
//!
//! `validate` reads the world and one proposed event, and it
//! answers with every reason the event cannot land. Not the first
//! reason: EVERY reason. One retry then fixes everything, instead
//! of one round trip for each mistake.
//!
//! So no check returns early. Each one adds to the list and the
//! next one runs.
//!
//! The two layers are not alternatives. The vocabulary in the
//! prompt catches the SHAPE of a proposal before the model runs,
//! and a rejection catches the SITUATION, which no text up front
//! can prevent. Ashford already has a king. Ada is dead.

use crate::event::EventKind;
use crate::fact::{Count, Fact, FactRules, FactVocabulary, Shape, LOCATED_IN};
use crate::reject::{Contradiction, Malformed, Rejection};
use crate::time::{EntityId, Tick};
use crate::world::{name_index, single_target, slot_index, World};

/// Every reason this event cannot land. An empty answer means it
/// can.
///
/// A local never takes the name of a module (`entity`, `world`):
/// Aeneas writes the same name for both, and the Lean breaks. So the
/// world is `w` and the entity is `who`.
#[cfg_attr(charon, verify::start_from)]
pub fn validate(w: &World, tick: Tick, kind: &EventKind) -> Vec<Rejection> {
    let mut out = Vec::new();
    if tick < w.tick {
        out.push(Rejection::Contradiction(Contradiction::TimeMovedBack {
            was: w.tick,
            got: tick,
        }));
    }
    match kind {
        EventKind::EntityCreated { id, name, .. } => {
            if queries::blank(name) {
                out.push(Rejection::Malformed(Malformed::UnnamedEntity { id: *id }));
            }
            if w.entity(*id).is_some() {
                out.push(Rejection::Contradiction(Contradiction::IdInUse { id: *id }));
            }
        }
        EventKind::EntityDestroyed { id } => match w.entity(*id) {
            None => out.push(Rejection::Contradiction(Contradiction::UnknownEntity {
                id: *id,
            })),
            Some(row) => {
                if row.gone() {
                    out.push(Rejection::Contradiction(Contradiction::Gone { id: *id }));
                }
            }
        },
        EventKind::FactStart {
            entity: who,
            name,
            value,
            linked_to,
        } => start(w, *who, name, *value, *linked_to, &mut out),
        EventKind::FactUpdate {
            entity: who,
            name,
            linked_to,
            from,
            to,
        } => update(w, *who, name, *linked_to, *from, *to, &mut out),
        EventKind::FactEnd {
            entity: who,
            name,
            linked_to,
        } => end(w, *who, name, *linked_to, &mut out),
    }
    out
}

// ---------------------------------------------------------------
// FactStart
// ---------------------------------------------------------------

#[allow(clippy::ptr_arg)]
fn start(
    w: &World,
    who: EntityId,
    name: &String,
    value: Option<i64>,
    linked_to: Option<EntityId>,
    out: &mut Vec<Rejection>,
) {
    let holder = live_holder(w, who, out);
    let Some(rules) = w.vocabulary.rules_key(name) else {
        out.push(Rejection::Malformed(Malformed::UnknownFact { name: name.clone() }));
        return;
    };
    let shape = rules.shape();
    number_fits(name, shape, value, out);
    target_fits(name, rules, linked_to, out);

    if let Some(target) = linked_to {
        if target == who {
            out.push(Rejection::Contradiction(Contradiction::SelfReference {
                id: who,
            }));
        } else if w.entity(target).is_none() {
            out.push(Rejection::Contradiction(Contradiction::UnknownEntity {
                id: target,
            }));
        }
        // A link to the dead is legal. A grudge outlives the
        // person, and the history names the dead (spec decision
        // 9). Only the HOLDER must be alive.
        if rules.takes_target() {
            push_all(out, &queries::type_faults(w, who, name, rules, target));
            counts_fit(w, who, name, rules, target, out);
        }
        if queries::is_located_in(name) {
            if let Some(through) = queries::cycle_through(w, who, target) {
                out.push(Rejection::Contradiction(Contradiction::Cycle {
                    entity: who,
                    through,
                }));
            }
        }
    }

    if !holder {
        return;
    }
    // The direction, against what the world holds now. A best
    // depth that starts again at zero is the case this catches.
    let held = held_for_start(w, who, name, linked_to);
    let direction = shape.direction();
    match held {
        Some(held_value) => {
            if let (Some(was), Some(now)) = (held_value, value) {
                if !direction.allows(was, now) {
                    out.push(Rejection::Contradiction(Contradiction::Backward {
                        entity: who,
                        name: name.clone(),
                        direction,
                        held: Some(was),
                        proposed: Some(now),
                    }));
                }
            }
        }
        None => {
            if !direction.can_restart() && queries::ended_before(w, who, name) {
                out.push(Rejection::Contradiction(Contradiction::Backward {
                    entity: who,
                    name: name.clone(),
                    direction,
                    held: None,
                    proposed: value,
                }));
            }
        }
    }
}

// ---------------------------------------------------------------
// FactUpdate
// ---------------------------------------------------------------

#[allow(clippy::too_many_arguments, clippy::ptr_arg)]
fn update(
    w: &World,
    who: EntityId,
    name: &String,
    linked_to: Option<EntityId>,
    from: i64,
    to: i64,
    out: &mut Vec<Rejection>,
) {
    let holder = live_holder(w, who, out);
    let Some(rules) = w.vocabulary.rules_key(name) else {
        out.push(Rejection::Malformed(Malformed::UnknownFact { name: name.clone() }));
        return;
    };
    let shape = rules.shape();
    // A flag has no number to change. Changing a NAME is one fact
    // ending and another starting, because an update holds one
    // name (spec decision 33 and a half).
    match shape {
        Shape::Flag { .. } => out.push(Rejection::Malformed(Malformed::TakesNoNumber {
            name: name.clone(),
        })),
        Shape::Number { band, direction } => {
            if !band.holds(to) {
                out.push(Rejection::Malformed(Malformed::OutOfBand {
                    name: name.clone(),
                    value: to,
                    min: band.min,
                    max: band.max,
                }));
            }
            if !direction.allows(from, to) {
                out.push(Rejection::Malformed(Malformed::Backward {
                    name: name.clone(),
                    direction,
                    from: Some(from),
                    to: Some(to),
                }));
            }
        }
    }
    target_fits(name, rules, linked_to, out);
    if !holder {
        return;
    }
    match slot_value(w, who, name, linked_to) {
        None => out.push(Rejection::Contradiction(Contradiction::NoSuchFact {
            entity: who,
            name: name.clone(),
            linked_to,
        })),
        Some(held_value) => {
            // The stale check. A director reads a briefing,
            // thinks, and proposes. The world moved meanwhile.
            let got = held_value.unwrap_or(from);
            if held_value != Some(from) {
                out.push(Rejection::Contradiction(Contradiction::Stale {
                    entity: who,
                    name: name.clone(),
                    want: from,
                    got,
                }));
            }
        }
    }
}

// ---------------------------------------------------------------
// FactEnd
// ---------------------------------------------------------------

#[allow(clippy::ptr_arg)]
fn end(
    w: &World,
    who: EntityId,
    name: &String,
    linked_to: Option<EntityId>,
    out: &mut Vec<Rejection>,
) {
    // A fact ends on a dead entity. A crown does not outlive the
    // king (spec decision 9), so a gone holder passes here.
    if w.entity(who).is_none() {
        out.push(Rejection::Contradiction(Contradiction::UnknownEntity {
            id: who,
        }));
    }
    let Some(rules) = w.vocabulary.rules_key(name) else {
        out.push(Rejection::Malformed(Malformed::UnknownFact { name: name.clone() }));
        return;
    };
    let direction = rules.shape().direction();
    if !direction.can_end() {
        out.push(Rejection::Malformed(Malformed::Backward {
            name: name.clone(),
            direction,
            from: None,
            to: None,
        }));
    }
    target_fits(name, rules, linked_to, out);
    if w.entity(who).is_some() && slot_value(w, who, name, linked_to).is_none() {
        out.push(Rejection::Contradiction(Contradiction::NoSuchFact {
            entity: who,
            name: name.clone(),
            linked_to,
        }));
    }
}

// ---------------------------------------------------------------
// The shared checks
// ---------------------------------------------------------------

/// Is the entity here, and alive? A dead entity gains no facts.
fn live_holder(w: &World, who: EntityId, out: &mut Vec<Rejection>) -> bool {
    match w.entity(who) {
        None => {
            out.push(Rejection::Contradiction(Contradiction::UnknownEntity {
                id: who,
            }));
            false
        }
        Some(row) => {
            if row.gone() {
                out.push(Rejection::Contradiction(Contradiction::Gone { id: who }));
                return false;
            }
            true
        }
    }
}

/// The fact a start meets, as its value: the first fact of a
/// single-target name, or the first fact in the slot. Nothing when no
/// fact is there.
///
/// The `match` stays in place of `?` and `map`: the proofs model no
/// `Try` trait and no closure.
#[allow(clippy::ptr_arg, clippy::question_mark, clippy::manual_map)]
fn held_for_start(
    w: &World,
    who: EntityId,
    name: &String,
    linked_to: Option<EntityId>,
) -> Option<Option<i64>> {
    let row = match w.entity(who) {
        Some(row) => row,
        None => return None,
    };
    let at = if single_target(&w.vocabulary, name) {
        name_index(&row.facts, name)
    } else {
        slot_index(&row.facts, name, linked_to)
    };
    match at {
        Some(i) => Some(row.facts[i].value),
        None => None,
    }
}

/// The value of the first fact in the slot. Nothing when the entity or
/// the fact is not there.
#[allow(clippy::ptr_arg, clippy::question_mark, clippy::manual_map)]
fn slot_value(
    w: &World,
    who: EntityId,
    name: &String,
    linked_to: Option<EntityId>,
) -> Option<Option<i64>> {
    let row = match w.entity(who) {
        Some(row) => row,
        None => return None,
    };
    match slot_index(&row.facts, name, linked_to) {
        Some(i) => Some(row.facts[i].value),
        None => None,
    }
}

/// Add each fault of the list, in order.
fn push_all(out: &mut Vec<Rejection>, faults: &[Rejection]) {
    let mut i = 0;
    while i < faults.len() {
        out.push(faults[i].clone());
        i += 1;
    }
}

#[allow(clippy::ptr_arg)]
fn number_fits(name: &String, shape: Shape, value: Option<i64>, out: &mut Vec<Rejection>) {
    match (shape, value) {
        (Shape::Number { .. }, None) => out.push(Rejection::Malformed(Malformed::NeedsNumber {
            name: name.clone(),
        })),
        (Shape::Flag { .. }, Some(_)) => out.push(Rejection::Malformed(Malformed::TakesNoNumber {
            name: name.clone(),
        })),
        (Shape::Number { band, .. }, Some(n)) => {
            if !band.holds(n) {
                out.push(Rejection::Malformed(Malformed::OutOfBand {
                    name: name.clone(),
                    value: n,
                    min: band.min,
                    max: band.max,
                }));
            }
        }
        (Shape::Flag { .. }, None) => {}
    }
}

#[allow(clippy::ptr_arg)]
fn target_fits(
    name: &String,
    rules: &FactRules,
    linked_to: Option<EntityId>,
    out: &mut Vec<Rejection>,
) {
    match (rules.takes_target(), linked_to) {
        (true, None) => out.push(Rejection::Malformed(Malformed::NeedsTarget {
            name: name.clone(),
        })),
        (false, Some(_)) => out.push(Rejection::Malformed(Malformed::TakesNoTarget {
            name: name.clone(),
        })),
        _ => {}
    }
}

/// The world queries of the gate. Each one only reads the world and
/// answers a value, and none of them touches the list of faults. The
/// Lean proofs keep this module opaque, so a law about `validate`
/// holds for every answer these queries give.
mod queries {
    use super::types_fit;
    use crate::fact::{FactRules, LOCATED_IN};
    use crate::reject::Rejection;
    use crate::time::EntityId;
    use crate::world::World;

    /// A name with nothing in it but white space.
    #[allow(clippy::ptr_arg)]
    pub(super) fn blank(name: &String) -> bool {
        name.trim().is_empty()
    }

    #[allow(clippy::ptr_arg)]
    pub(super) fn is_located_in(name: &String) -> bool {
        name == LOCATED_IN
    }

    pub(super) fn cycle_through(w: &World, who: EntityId, target: EntityId) -> Option<EntityId> {
        w.would_cycle(who, target)
    }

    #[allow(clippy::ptr_arg)]
    pub(super) fn type_faults(
        w: &World,
        who: EntityId,
        name: &String,
        rules: &FactRules,
        target: EntityId,
    ) -> Vec<Rejection> {
        let mut out = Vec::new();
        types_fit(w, who, name, rules, target, &mut out);
        out
    }

    #[allow(clippy::ptr_arg)]
    pub(super) fn ended_before(w: &World, who: EntityId, name: &String) -> bool {
        w.ever_ended(who, name)
    }
}

fn types_fit(
    world: &World,
    entity: EntityId,
    name: &str,
    rules: &FactRules,
    target: EntityId,
    out: &mut Vec<Rejection>,
) {
    let (Some(holder), Some(goes_to)) = (world.type_of(entity), world.type_of(target)) else {
        return;
    };
    if !rules.type_allowed(holder, goes_to) {
        out.push(Rejection::Malformed(Malformed::TypeNotAllowed {
            name: name.to_string(),
            holder,
            target: goes_to,
        }));
    }
}

#[allow(clippy::ptr_arg)]
fn counts_fit(
    w: &World,
    who: EntityId,
    name: &String,
    rules: &FactRules,
    target: EntityId,
    out: &mut Vec<Rejection>,
) {
    let (holders, targets) = match rules {
        FactRules::Linked {
            holders, targets, ..
        } => (*holders, *targets),
        FactRules::Solo(_) => return,
    };
    // The holder side never makes room. Ending the crown of Ada
    // is a change to ANOTHER entity, and this event names one.
    if let Some(limit) = holders.limit() {
        let held_by = holders_except(w, name, target, who);
        // One more holder does not fit: `len + 1 > limit`, with no add.
        if held_by.len() >= usize::from(limit) {
            out.push(Rejection::Contradiction(Contradiction::TooManyHolders {
                name: name.clone(),
                target,
                held_by,
                limit,
            }));
        }
    }
    // The target side makes room when, and only when, the count
    // is exactly one: then there is one fact to close and no
    // choice about which (spec decision 32, the move).
    if let Some(limit) = targets.limit() {
        if targets == Count::One || limit == 1 {
            return;
        }
        let pointing_at = targets_except(w, who, name, target);
        if pointing_at.len() >= usize::from(limit) {
            out.push(Rejection::Contradiction(Contradiction::TooManyTargets {
                name: name.clone(),
                holder: who,
                pointing_at,
                limit,
            }));
        }
    }
}

/// The entities other than `who` that hold the name about the target,
/// in ascending id order.
#[allow(clippy::ptr_arg)]
fn holders_except(w: &World, name: &String, target: EntityId, who: EntityId) -> Vec<EntityId> {
    let ids = w.entity_ids();
    let mut out = Vec::new();
    let mut i = 0;
    while i < ids.len() {
        push_holder(&mut out, w, ids[i], name, target, who);
        i += 1;
    }
    out
}

/// One step of `holders_except`. A loop body of its own, because Aeneas
/// stops on a branch inside a loop that holds a borrow.
#[allow(clippy::ptr_arg)]
fn push_holder(
    out: &mut Vec<EntityId>,
    w: &World,
    id: EntityId,
    name: &String,
    target: EntityId,
    who: EntityId,
) {
    if let Some(row) = w.entity(id) {
        if row.id != who && slot_index(&row.facts, name, Some(target)).is_some() {
            out.push(row.id);
        }
    }
}

/// The targets other than `target` that `who` holds the name about, in
/// the order of its facts.
#[allow(clippy::ptr_arg)]
fn targets_except(w: &World, who: EntityId, name: &String, target: EntityId) -> Vec<EntityId> {
    let mut out = Vec::new();
    let row = match w.entity(who) {
        Some(row) => row,
        None => return out,
    };
    let mut i = 0;
    while i < row.facts.len() {
        push_other_target(&mut out, &row.facts[i], name, target);
        i += 1;
    }
    out
}

/// One step of `targets_except`, a loop body of its own for the same
/// reason as `push_holder`.
#[allow(clippy::ptr_arg)]
fn push_other_target(out: &mut Vec<EntityId>, f: &Fact, name: &String, target: EntityId) {
    if f.name == *name {
        if let Some(t) = f.linked_to {
            if t != target {
                out.push(t);
            }
        }
    }
}

/// Is the vocabulary itself sound? A caller writes it, so a
/// caller can be wrong.
pub fn vocabulary_sound(vocabulary: &FactVocabulary) -> Vec<Rejection> {
    let mut out = Vec::new();
    for (name, rules) in vocabulary.names() {
        if name.trim().is_empty() {
            out.push(Rejection::Malformed(Malformed::BrokenVocabulary {
                name: name.clone(),
                fault: "a fact carries no name".to_string(),
            }));
        }
        if let Some(band) = rules.shape().band() {
            if band.empty() {
                out.push(Rejection::Malformed(Malformed::BrokenVocabulary {
                    name: name.clone(),
                    fault: "the band holds no number".to_string(),
                }));
            }
        }
        if let FactRules::Linked {
            holders, targets, ..
        } = rules
        {
            for (side, count) in [("holders", holders), ("targets", targets)] {
                if count.limit() == Some(0) {
                    out.push(Rejection::Malformed(Malformed::BrokenVocabulary {
                        name: name.clone(),
                        fault: format!("a count of zero on the {side} forbids the name"),
                    }));
                }
            }
        }
        if name == LOCATED_IN && !rules.same_fold(&crate::fact::located_in_rules()) {
            out.push(Rejection::Malformed(Malformed::BrokenVocabulary {
                name: name.clone(),
                fault: "the crate declares located_in".to_string(),
            }));
        }
    }
    out
}
