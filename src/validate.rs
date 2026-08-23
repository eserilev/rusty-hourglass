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
use crate::fact::{Count, FactRules, FactVocabulary, Shape, LOCATED_IN};
use crate::reject::{Contradiction, Malformed, Rejection};
use crate::time::{EntityId, Tick};
use crate::world::World;

/// Every reason this event cannot land. An empty answer means it
/// can.
pub fn validate(world: &World, tick: Tick, kind: &EventKind) -> Vec<Rejection> {
    let mut out = Vec::new();
    if tick < world.tick {
        out.push(Rejection::Contradiction(Contradiction::TimeMovedBack {
            was: world.tick,
            got: tick,
        }));
    }
    match kind {
        EventKind::EntityCreated { id, name, .. } => {
            if name.trim().is_empty() {
                out.push(Rejection::Malformed(Malformed::UnnamedEntity { id: *id }));
            }
            if world.entity(*id).is_some() {
                out.push(Rejection::Contradiction(Contradiction::IdInUse { id: *id }));
            }
        }
        EventKind::EntityDestroyed { id } => match world.entity(*id) {
            None => out.push(Rejection::Contradiction(Contradiction::UnknownEntity {
                id: *id,
            })),
            Some(entity) => {
                if entity.gone() {
                    out.push(Rejection::Contradiction(Contradiction::Gone { id: *id }));
                }
            }
        },
        EventKind::FactStart {
            entity,
            name,
            value,
            linked_to,
        } => start(world, *entity, name, *value, *linked_to, &mut out),
        EventKind::FactUpdate {
            entity,
            name,
            linked_to,
            from,
            to,
        } => update(world, *entity, name, *linked_to, *from, *to, &mut out),
        EventKind::FactEnd {
            entity,
            name,
            linked_to,
        } => end(world, *entity, name, *linked_to, &mut out),
    }
    out
}

// ---------------------------------------------------------------
// FactStart
// ---------------------------------------------------------------

fn start(
    world: &World,
    entity: EntityId,
    name: &str,
    value: Option<i64>,
    linked_to: Option<EntityId>,
    out: &mut Vec<Rejection>,
) {
    let holder = live_holder(world, entity, out);
    let Some(rules) = world.vocabulary.rules(name) else {
        out.push(Rejection::Malformed(Malformed::UnknownFact {
            name: name.to_string(),
        }));
        return;
    };
    let shape = rules.shape();
    number_fits(name, shape, value, out);
    target_fits(name, rules, linked_to, out);

    if let Some(target) = linked_to {
        if target == entity {
            out.push(Rejection::Contradiction(Contradiction::SelfReference {
                id: entity,
            }));
        } else if world.entity(target).is_none() {
            out.push(Rejection::Contradiction(Contradiction::UnknownEntity {
                id: target,
            }));
        }
        // A link to the dead is legal. A grudge outlives the
        // person, and the history names the dead (spec decision
        // 9). Only the HOLDER must be alive.
        if rules.takes_target() {
            types_fit(world, entity, name, rules, target, out);
            counts_fit(world, entity, name, rules, target, out);
        }
        if name == LOCATED_IN {
            if let Some(through) = world.would_cycle(entity, target) {
                out.push(Rejection::Contradiction(Contradiction::Cycle {
                    entity,
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
    let held = match world.target_count(name) {
        Some(count) if count.is_single() => world
            .entity(entity)
            .and_then(|e| e.facts_named(name).next()),
        _ => world.entity(entity).and_then(|e| e.fact(name, linked_to)),
    };
    let direction = shape.direction();
    match held {
        Some(fact) => {
            if let (Some(was), Some(now)) = (fact.value, value) {
                if !direction.allows(was, now) {
                    out.push(Rejection::Contradiction(Contradiction::Backward {
                        entity,
                        name: name.to_string(),
                        direction,
                        held: Some(was),
                        proposed: Some(now),
                    }));
                }
            }
        }
        None => {
            if !direction.can_restart() && world.ever_ended(entity, name) {
                out.push(Rejection::Contradiction(Contradiction::Backward {
                    entity,
                    name: name.to_string(),
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

#[allow(clippy::too_many_arguments)]
fn update(
    world: &World,
    entity: EntityId,
    name: &str,
    linked_to: Option<EntityId>,
    from: i64,
    to: i64,
    out: &mut Vec<Rejection>,
) {
    let holder = live_holder(world, entity, out);
    let Some(rules) = world.vocabulary.rules(name) else {
        out.push(Rejection::Malformed(Malformed::UnknownFact {
            name: name.to_string(),
        }));
        return;
    };
    let shape = rules.shape();
    // A flag has no number to change. Changing a NAME is one fact
    // ending and another starting, because an update holds one
    // name (spec decision 33 and a half).
    match shape {
        Shape::Flag { .. } => out.push(Rejection::Malformed(Malformed::TakesNoNumber {
            name: name.to_string(),
        })),
        Shape::Number { band, direction } => {
            if !band.holds(to) {
                out.push(Rejection::Malformed(Malformed::OutOfBand {
                    name: name.to_string(),
                    value: to,
                    min: band.min,
                    max: band.max,
                }));
            }
            if !direction.allows(from, to) {
                out.push(Rejection::Malformed(Malformed::Backward {
                    name: name.to_string(),
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
    match world.entity(entity).and_then(|e| e.fact(name, linked_to)) {
        None => out.push(Rejection::Contradiction(Contradiction::NoSuchFact {
            entity,
            name: name.to_string(),
            linked_to,
        })),
        Some(fact) => {
            // The stale check. A director reads a briefing,
            // thinks, and proposes. The world moved meanwhile.
            let got = fact.value.unwrap_or(from);
            if fact.value != Some(from) {
                out.push(Rejection::Contradiction(Contradiction::Stale {
                    entity,
                    name: name.to_string(),
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

fn end(
    world: &World,
    entity: EntityId,
    name: &str,
    linked_to: Option<EntityId>,
    out: &mut Vec<Rejection>,
) {
    // A fact ends on a dead entity. A crown does not outlive the
    // king (spec decision 9), so a gone holder passes here.
    if world.entity(entity).is_none() {
        out.push(Rejection::Contradiction(Contradiction::UnknownEntity {
            id: entity,
        }));
    }
    let Some(rules) = world.vocabulary.rules(name) else {
        out.push(Rejection::Malformed(Malformed::UnknownFact {
            name: name.to_string(),
        }));
        return;
    };
    let direction = rules.shape().direction();
    if !direction.can_end() {
        out.push(Rejection::Malformed(Malformed::Backward {
            name: name.to_string(),
            direction,
            from: None,
            to: None,
        }));
    }
    target_fits(name, rules, linked_to, out);
    if let Some(row) = world.entity(entity) {
        if row.fact(name, linked_to).is_none() {
            out.push(Rejection::Contradiction(Contradiction::NoSuchFact {
                entity,
                name: name.to_string(),
                linked_to,
            }));
        }
    }
}

// ---------------------------------------------------------------
// The shared checks
// ---------------------------------------------------------------

/// Is the entity here, and alive? A dead entity gains no facts.
fn live_holder(world: &World, entity: EntityId, out: &mut Vec<Rejection>) -> bool {
    match world.entity(entity) {
        None => {
            out.push(Rejection::Contradiction(Contradiction::UnknownEntity {
                id: entity,
            }));
            false
        }
        Some(row) => {
            if row.gone() {
                out.push(Rejection::Contradiction(Contradiction::Gone { id: entity }));
                return false;
            }
            true
        }
    }
}

fn number_fits(name: &str, shape: Shape, value: Option<i64>, out: &mut Vec<Rejection>) {
    match (shape, value) {
        (Shape::Number { .. }, None) => out.push(Rejection::Malformed(Malformed::NeedsNumber {
            name: name.to_string(),
        })),
        (Shape::Flag { .. }, Some(_)) => out.push(Rejection::Malformed(Malformed::TakesNoNumber {
            name: name.to_string(),
        })),
        (Shape::Number { band, .. }, Some(n)) => {
            if !band.holds(n) {
                out.push(Rejection::Malformed(Malformed::OutOfBand {
                    name: name.to_string(),
                    value: n,
                    min: band.min,
                    max: band.max,
                }));
            }
        }
        (Shape::Flag { .. }, None) => {}
    }
}

fn target_fits(
    name: &str,
    rules: &FactRules,
    linked_to: Option<EntityId>,
    out: &mut Vec<Rejection>,
) {
    match (rules.takes_target(), linked_to) {
        (true, None) => out.push(Rejection::Malformed(Malformed::NeedsTarget {
            name: name.to_string(),
        })),
        (false, Some(_)) => out.push(Rejection::Malformed(Malformed::TakesNoTarget {
            name: name.to_string(),
        })),
        _ => {}
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

fn counts_fit(
    world: &World,
    entity: EntityId,
    name: &str,
    rules: &FactRules,
    target: EntityId,
    out: &mut Vec<Rejection>,
) {
    let FactRules::Linked {
        holders, targets, ..
    } = rules
    else {
        return;
    };
    // The holder side never makes room. Ending the crown of Ada
    // is a change to ANOTHER entity, and this event names one.
    if let Some(limit) = holders.limit() {
        let held_by: Vec<EntityId> = world
            .holders_of(name, target)
            .into_iter()
            .filter(|id| *id != entity)
            .collect();
        if held_by.len() as u64 + 1 > u64::from(limit) {
            out.push(Rejection::Contradiction(Contradiction::TooManyHolders {
                name: name.to_string(),
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
        if *targets == Count::One || limit == 1 {
            return;
        }
        let pointing_at: Vec<EntityId> = world
            .targets_of(name, entity)
            .into_iter()
            .filter(|id| *id != target)
            .collect();
        if pointing_at.len() as u64 + 1 > u64::from(limit) {
            out.push(Rejection::Contradiction(Contradiction::TooManyTargets {
                name: name.to_string(),
                holder: entity,
                pointing_at,
                limit,
            }));
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
