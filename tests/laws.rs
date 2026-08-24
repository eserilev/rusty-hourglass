//! The laws, over a seeded sweep.
//!
//! Two claims, and each one is checked against an oracle that
//! shares no line with the crate.
//!
//! **The merge is a join.** It is commutative, associative, and
//! idempotent, an empty record is its start, and it never moves a
//! field backward. Those five together are what let a server
//! merge two devices in any order, as often as it likes, and lose
//! nothing.
//!
//! **The gate holds the world.** For every proposal, `propose`
//! refuses, or `verify` passes on the world it leaves behind.
//!
//! The draws come from a seeded generator, so a failure replays
//! exactly. The tests read no clock and call no system random
//! source.

use hourglass::*;

/// A seeded generator.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Three up numbers, one down number, and two up flags.
const NUMBERS: [(&str, i64, i64); 4] = [
    ("best_depth", 0, 60),
    ("runs", 0, 500),
    ("best_gold", 0, 9_000),
    ("lives_left", 0, 9),
];
const FLAGS: [&str; 2] = ["unlocked_bow", "unlocked_map"];

fn schema() -> FactVocabulary {
    let mut v = FactVocabulary::new(1);
    for (name, min, max) in NUMBERS {
        let direction = if name == "lives_left" {
            Direction::Down
        } else {
            Direction::Up
        };
        v.declare(
            name,
            FactRules::solo(Shape::number(Band::new(min, max)).moving(direction)),
        );
    }
    for name in FLAGS {
        v.declare(name, FactRules::solo(Shape::flag().moving(Direction::Up)));
    }
    v
}

/// One record of random fields, every value inside its band.
fn draw(rng: &mut Lcg) -> Record {
    let mut out = Record::new();
    for (name, min, max) in NUMBERS {
        if rng.below(3) > 0 {
            let span = (max - min + 1) as u64;
            out.set(name, Value::Number(min + rng.below(span) as i64));
        }
    }
    for name in FLAGS {
        // One third true, one third absent, one third written false.
        // A false flag leaves the record on write, so the sweep
        // sees the one-shape law from the write side too.
        match rng.below(3) {
            0 => out.set(name, Value::Flag(true)),
            1 => out.set(name, Value::Flag(false)),
            _ => &mut out,
        };
    }
    out
}

/// The naive oracle. It reads the two records as plain lists and
/// folds them by hand, with no schema lookup and no `Join`.
fn oracle(a: &Record, b: &Record) -> Vec<(String, Value)> {
    let mut out: Vec<(String, Value)> = Vec::new();
    for (name, min, max) in NUMBERS {
        let _ = (min, max);
        let x = a.number(name);
        let y = b.number(name);
        let got = match (x, y) {
            (Some(p), Some(q)) => {
                if name == "lives_left" {
                    Some(if p < q { p } else { q })
                } else {
                    Some(if p > q { p } else { q })
                }
            }
            (Some(p), None) => Some(p),
            (None, Some(q)) => Some(q),
            (None, None) => None,
        };
        if let Some(n) = got {
            out.push((name.to_string(), Value::Number(n)));
        }
    }
    for name in FLAGS {
        if a.flag(name) || b.flag(name) {
            out.push((name.to_string(), Value::Flag(true)));
        }
    }
    out.sort_by(|p, q| p.0.cmp(&q.0));
    out
}

fn as_pairs(record: &Record) -> Vec<(String, Value)> {
    record.names().map(|(n, v)| (n.clone(), *v)).collect()
}

fn join(a: &Record, b: &Record) -> Record {
    merge(&schema(), a, b).expect("a drawn record fits the schema")
}

// ---------------------------------------------------------------
// The five merge laws
// ---------------------------------------------------------------

#[test]
fn the_merge_answers_the_same_either_way() {
    let mut rng = Lcg(20_260_817);
    for _ in 0..400 {
        let a = draw(&mut rng);
        let b = draw(&mut rng);
        assert_eq!(join(&a, &b), join(&b, &a), "a: {a:?} b: {b:?}");
        // And the answer matches the oracle.
        assert_eq!(as_pairs(&join(&a, &b)), oracle(&a, &b));
    }
}

#[test]
fn the_merge_ignores_the_grouping() {
    let mut rng = Lcg(7);
    for _ in 0..400 {
        let a = draw(&mut rng);
        let b = draw(&mut rng);
        let c = draw(&mut rng);
        let left = join(&join(&a, &b), &c);
        let right = join(&a, &join(&b, &c));
        assert_eq!(left, right, "a: {a:?} b: {b:?} c: {c:?}");
    }
}

#[test]
fn the_merge_of_a_record_with_itself_is_that_record() {
    let mut rng = Lcg(99);
    for _ in 0..400 {
        let a = draw(&mut rng);
        assert_eq!(join(&a, &a), a);
        // A merge that runs twice answers what it answered once.
        let b = draw(&mut rng);
        let once = join(&a, &b);
        assert_eq!(join(&once, &b), once);
        assert_eq!(join(&once, &once), once);
    }
}

#[test]
fn an_empty_record_changes_nothing() {
    let mut rng = Lcg(1_234);
    let empty = Record::new();
    for _ in 0..400 {
        let a = draw(&mut rng);
        assert_eq!(join(&a, &empty), a);
        assert_eq!(join(&empty, &a), a);
    }
    assert!(join(&empty, &empty).is_empty());
}

#[test]
fn the_merge_never_moves_a_field_backward() {
    let mut rng = Lcg(555);
    for _ in 0..400 {
        let a = draw(&mut rng);
        let b = draw(&mut rng);
        let got = join(&a, &b);
        for side in [&a, &b] {
            for (name, value) in side.names() {
                match value {
                    Value::Number(n) => {
                        let after = got.number(name).expect("the name survives the merge");
                        if name == "lives_left" {
                            assert!(after <= *n);
                        } else {
                            assert!(after >= *n);
                        }
                    }
                    Value::Flag(_) => assert!(got.flag(name), "{name} was lost"),
                }
            }
        }
        // The merge invents no name, and every number keeps its
        // band.
        assert!(check(&schema(), &got).is_empty());
        for (name, _) in got.names() {
            assert!(a.get(name).is_some() || b.get(name).is_some());
        }
    }
}

// ---------------------------------------------------------------
// The gate holds the world
// ---------------------------------------------------------------

const CAST: usize = 6;

fn world_schema() -> FactVocabulary {
    let mut v = schema();
    v.version = 1;
    v.declare("burned", FactRules::solo(Shape::flag()));
    v.declare(
        "treasury",
        FactRules::solo(Shape::number(Band::new(0, 9_000))),
    );
    v.declare(
        "king_of",
        FactRules::linked(Shape::flag(), Count::One, Count::Many)
            .allowing(EntityType::Person, &[EntityType::Place]),
    );
    v.declare(
        "hates",
        FactRules::linked(Shape::number(Band::new(0, 10)), Count::Many, Count::Many),
    );
    v.declare(
        "council_of",
        FactRules::linked(Shape::flag(), Count::AtMost(3), Count::AtMost(2))
            .allowing(EntityType::Person, &[EntityType::Place]),
    );
    v
}

fn peopled() -> World {
    let mut w = World::new(world_schema());
    let kinds = [
        EntityType::Person,
        EntityType::Place,
        EntityType::Place,
        EntityType::Person,
        EntityType::Thing,
        EntityType::Faction,
    ];
    for (i, kind) in kinds.iter().enumerate() {
        w.propose(
            Tick(1),
            EventKind::EntityCreated {
                id: EntityId(i as u32),
                entity_type: *kind,
                name: format!("thing {i}"),
            },
        )
        .expect("the cast is legal");
    }
    w
}

/// One random proposal. Most are junk, and that is the point.
fn proposal(rng: &mut Lcg) -> EventKind {
    let who = EntityId(rng.below(CAST as u64 + 1) as u32);
    let at = EntityId(rng.below(CAST as u64 + 1) as u32);
    let names = [
        "best_depth",
        "runs",
        "lives_left",
        "unlocked_bow",
        "burned",
        "treasury",
        "king_of",
        "hates",
        "council_of",
        LOCATED_IN,
        "treasure",
    ];
    let name = names[rng.below(names.len() as u64) as usize].to_string();
    let value = if rng.below(2) == 0 {
        Some(rng.below(80) as i64 - 8)
    } else {
        None
    };
    let target = if rng.below(2) == 0 { Some(at) } else { None };
    match rng.below(10) {
        0 => EventKind::EntityCreated {
            id: EntityId(rng.below(CAST as u64 + 2) as u32),
            entity_type: EntityType::Person,
            name: "a new one".to_string(),
        },
        1 => EventKind::EntityDestroyed { id: who },
        2 | 3 => EventKind::FactEnd {
            entity: who,
            name,
            linked_to: target,
        },
        4 | 5 => EventKind::FactUpdate {
            entity: who,
            name,
            linked_to: target,
            from: rng.below(40) as i64,
            to: rng.below(40) as i64,
        },
        _ => EventKind::FactStart {
            entity: who,
            name,
            value,
            linked_to: target,
        },
    }
}

#[test]
fn a_seeded_sweep_of_proposals_keeps_every_invariant() {
    let mut landed = 0;
    let mut refused = 0;
    for seed in 0..40u64 {
        let mut rng = Lcg(seed.wrapping_mul(2_654_435_761).wrapping_add(11));
        let mut w = peopled();
        for step in 0..60 {
            let kind = proposal(&mut rng);
            let before = w.clone();
            match w.propose(Tick(2 + step / 6), kind.clone()) {
                Ok(_) => landed += 1,
                Err(faults) => {
                    refused += 1;
                    assert!(!faults.is_empty());
                    // A refused proposal changes nothing at all.
                    assert_eq!(w, before, "seed {seed} step {step} on {kind:?}");
                }
            }
            // The claim, after every step: the world obeys every
            // invariant of the spec.
            assert!(verify(&w), "seed {seed} step {step} on {kind:?}");
        }
    }
    // The sweep is worth running only if both paths ran.
    assert!(landed > 200, "only {landed} landed");
    assert!(refused > 200, "only {refused} were refused");
}

#[test]
fn every_accepted_history_replays_to_the_same_state() {
    for seed in 0..20u64 {
        let mut rng = Lcg(seed.wrapping_mul(48_271).wrapping_add(3));
        let mut w = peopled();
        for step in 0..60 {
            let _ = w.propose(Tick(2 + step / 6), proposal(&mut rng));
        }
        let again = World::replay(world_schema(), w.history());
        assert_eq!(again, w, "seed {seed}");
        // And a rollback to any cut equals a replay of the prefix.
        if w.history().len() > 4 {
            let cut = EventId((w.history().len() / 2) as u64);
            let mut rolled = w.clone();
            rolled.rewind(cut);
            assert_eq!(rolled.history().len(), cut.0 as usize + 1);
            assert!(verify(&rolled), "seed {seed}");
        }
    }
}

#[test]
fn the_referee_catches_what_the_gate_would_have_refused() {
    // `commit` skips the gate, so it builds the worlds that must
    // never exist. A referee that passed these proves nothing.
    let clean = peopled();
    assert!(verify(&clean));

    let mut alien = peopled();
    alien.commit(
        Tick(2),
        EventKind::FactStart {
            entity: EntityId(0),
            name: "treasure".to_string(),
            value: None,
            linked_to: None,
        },
    );
    assert!(!verify(&alien), "an undeclared name must fail");

    let mut over_band = peopled();
    over_band.commit(
        Tick(2),
        EventKind::FactStart {
            entity: EntityId(0),
            name: "best_depth".to_string(),
            value: Some(9_000),
            linked_to: None,
        },
    );
    assert!(!verify(&over_band), "a band break must fail");

    let mut ring = peopled();
    for (who, at) in [(1u32, 2u32), (2, 1)] {
        ring.commit(
            Tick(2),
            EventKind::FactStart {
                entity: EntityId(who),
                name: LOCATED_IN.to_string(),
                value: None,
                linked_to: Some(EntityId(at)),
            },
        );
    }
    assert!(!verify(&ring), "a ring of places must fail");

    let mut two_kings = peopled();
    for who in [0u32, 3] {
        two_kings.commit(
            Tick(2),
            EventKind::FactStart {
                entity: EntityId(who),
                name: "king_of".to_string(),
                value: None,
                linked_to: Some(EntityId(1)),
            },
        );
    }
    assert!(!verify(&two_kings), "two kings must fail");

    let mut wrong_type = peopled();
    wrong_type.commit(
        Tick(2),
        EventKind::FactStart {
            entity: EntityId(4),
            name: "king_of".to_string(),
            value: None,
            linked_to: Some(EntityId(1)),
        },
    );
    assert!(!verify(&wrong_type), "a sword on a throne must fail");
}

// ---------------------------------------------------------------
// The briefing
// ---------------------------------------------------------------

#[test]
fn a_briefing_holds_the_present_and_a_tail_of_the_history() {
    let mut rng = Lcg(31);
    let mut w = peopled();
    for step in 0..40 {
        let _ = w.propose(Tick(2 + step / 6), proposal(&mut rng));
    }
    let brief = w.brief(Some(EntityId(3)), Budget::new(4, 3));
    // The subject is always in its own briefing.
    assert_eq!(brief.entities.first(), Some(&EntityId(3)));
    assert_eq!(brief.entities.len(), 4);
    assert_eq!(brief.recent.len(), 3);
    // The entities carry the present. The events carry the tail.
    for id in &brief.entities {
        assert!(w.entity(*id).is_some());
    }
    let last = w.history().len() as u64 - 1;
    assert_eq!(brief.recent.last(), Some(&EventId(last)));
    // A budget bigger than the world takes the whole world.
    let all = w.brief(None, Budget::new(50, 50));
    assert_eq!(all.entities.len(), w.entities().count());
    assert_eq!(all.recent.len(), w.history().len());
}

#[test]
fn every_rejection_writes_its_own_line() {
    let mut rng = Lcg(4_242);
    let mut w = peopled();
    let mut lines: Vec<String> = Vec::new();
    for step in 0..300 {
        if let Err(faults) = w.propose(Tick(2 + step / 30), proposal(&mut rng)) {
            for fault in faults {
                let line = fault.to_string();
                assert!(!line.is_empty());
                // The line is a default, and it holds no markup
                // and no leftover of a format string.
                assert!(!line.contains('{'));
                lines.push(line);
            }
        }
    }
    lines.sort();
    lines.dedup();
    assert!(lines.len() > 8, "only {} kinds of line", lines.len());
}
