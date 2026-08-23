//! The memory of a run: the roguelike seam, and the schema that
//! grows.
//!
//! The flow of a server is four lines, and every line is here:
//!
//! ```text
//! let now    = world.record(runner);        // what the device holds
//! let merged = merge(&schema, &now, &run)?; // the run just ended
//! let events = writes(&world, runner, &merged);
//! for e in events { world.propose(tick, e)?; }
//! ```

use hourglass::*;

const RUNNER: EntityId = EntityId(0);
const CAVE: EntityId = EntityId(1);

/// The memory schema of the dungeon. Caller data, all of it.
fn schema(version: u32) -> FactVocabulary {
    let mut v = FactVocabulary::new(version);
    v.declare(
        "best_depth",
        FactRules::solo(Shape::number(Band::new(0, 60)).moving(Direction::Up)),
    );
    v.declare(
        "runs",
        FactRules::solo(Shape::number(Band::new(0, 100_000)).moving(Direction::Up)),
    );
    v.declare(
        "unlocked_bow",
        FactRules::solo(Shape::flag().moving(Direction::Up)),
    );
    v
}

/// The same schema, plus the one number a kid asked for later.
fn schema_v2() -> FactVocabulary {
    let mut v = schema(2);
    v.declare(
        "best_gold",
        FactRules::solo(Shape::number(Band::new(0, 999_999)).moving(Direction::Up)),
    );
    v
}

fn world() -> World {
    let mut w = World::new(schema(1));
    w.propose(
        Tick(1),
        EventKind::EntityCreated {
            id: RUNNER,
            entity_type: EntityType::Person,
            name: "the runner".to_string(),
        },
    )
    .expect("the runner is legal");
    w.propose(
        Tick(1),
        EventKind::EntityCreated {
            id: CAVE,
            entity_type: EntityType::Place,
            name: "the cave".to_string(),
        },
    )
    .expect("the cave is legal");
    w
}

fn record(pairs: &[(&str, Value)]) -> Record {
    let mut out = Record::new();
    for (name, value) in pairs {
        out.set(name, *value);
    }
    out
}

/// Land a record on the world, the way a server does.
fn save(w: &mut World, tick: u64, run: &Record) -> usize {
    let schema = w.vocabulary.clone();
    let now = w.record(RUNNER);
    let merged = merge(&schema, &now, run).expect("the run fits the schema");
    let events = writes(w, RUNNER, &merged);
    let count = events.len();
    for event in events {
        w.propose(Tick(tick), event).expect("a forward write lands");
    }
    count
}

// ---------------------------------------------------------------
// The record and the seam
// ---------------------------------------------------------------

#[test]
fn a_record_is_the_flat_cut_of_one_entity() {
    let mut w = world();
    save(
        &mut w,
        2,
        &record(&[
            ("best_depth", Value::Number(7)),
            ("unlocked_bow", Value::Flag(true)),
        ]),
    );
    // A link is not in a record, so the place of the runner never
    // reaches the save.
    w.propose(
        Tick(2),
        EventKind::FactStart {
            entity: RUNNER,
            name: LOCATED_IN.to_string(),
            value: None,
            linked_to: Some(CAVE),
        },
    )
    .expect("the runner walks in");

    let got = w.record(RUNNER);
    assert_eq!(got.number("best_depth"), Some(7));
    assert!(got.flag("unlocked_bow"));
    assert_eq!(got.len(), 2);
    assert!(got.get(LOCATED_IN).is_none());
    assert!(verify(&w));
}

#[test]
fn a_record_reads_the_json_the_platform_stores() {
    // The shape `Game.progress` already writes into the player
    // scope: a flat object of numbers and flags.
    let text = r#"{"best_depth":7,"runs":12,"unlocked_bow":true}"#;
    let got: Record = serde_json::from_str(text).expect("a record reads back");
    assert_eq!(got.number("best_depth"), Some(7));
    assert_eq!(got.number("runs"), Some(12));
    assert!(got.flag("unlocked_bow"));
    assert!(check(&schema(1), &got).is_empty());
    let out = serde_json::to_string(&got).expect("a record writes as json");
    assert_eq!(out, text);
}

#[test]
fn a_flag_that_is_false_says_what_an_empty_record_says() {
    let got: Record = serde_json::from_str(r#"{"unlocked_bow":false}"#).expect("it reads back");
    assert!(!got.flag("unlocked_bow"));
    assert!(got.get("unlocked_bow").is_none());
    let merged = merge(&schema(1), &got, &Record::new()).expect("it merges");
    assert!(merged.is_empty());
}

// ---------------------------------------------------------------
// The three rejections the brief names
// ---------------------------------------------------------------

#[test]
fn an_alien_field_is_refused() {
    let alien = record(&[("best_dpeth", Value::Number(7))]);
    let faults = merge(&schema(1), &alien, &Record::new()).expect_err("an alien name is refused");
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::UnknownFact {
            name: "best_dpeth".to_string()
        })]
    );
}

#[test]
fn a_band_break_is_refused() {
    let deep = record(&[("best_depth", Value::Number(61))]);
    let faults = merge(&schema(1), &deep, &Record::new()).expect_err("a band break is refused");
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::OutOfBand {
            name: "best_depth".to_string(),
            value: 61,
            min: 0,
            max: 60,
        })]
    );
}

#[test]
fn a_wrong_shape_is_refused() {
    let wrong = record(&[
        ("best_depth", Value::Flag(true)),
        ("unlocked_bow", Value::Number(1)),
    ]);
    let faults = merge(&schema(1), &wrong, &Record::new()).expect_err("a wrong shape is refused");
    assert_eq!(faults.len(), 2);
    assert!(
        faults.contains(&Rejection::Malformed(Malformed::NeedsNumber {
            name: "best_depth".to_string()
        }))
    );
    assert!(
        faults.contains(&Rejection::Malformed(Malformed::TakesNoNumber {
            name: "unlocked_bow".to_string()
        }))
    );
}

#[test]
fn a_name_with_no_forward_order_cannot_merge() {
    let mut v = schema(1);
    v.declare("gold", FactRules::solo(Shape::number(Band::new(0, 100))));
    v.declare(
        "sealed",
        FactRules::solo(Shape::flag().moving(Direction::Down)),
    );
    // A free number has no later answer, a device that never
    // heard of a falling flag erases it, and a linked name has no
    // place in a flat record.
    for (name, why) in [
        ("gold", Unmergeable::NoDirection),
        ("sealed", Unmergeable::VanishingFlag),
        (LOCATED_IN, Unmergeable::TakesTarget),
    ] {
        let one = record(&[(name, Value::Flag(true))]);
        let faults = merge(&v, &one, &Record::new()).expect_err("it cannot merge");
        assert_eq!(
            faults,
            vec![Rejection::Malformed(Malformed::Unmergeable {
                name: name.to_string(),
                why,
            })],
            "{name} answered the wrong reason"
        );
    }
    // The names of a record leave the rest out.
    let names = memory_names(&v);
    assert!(names.contains(&"best_depth".to_string()));
    assert!(!names.contains(&"gold".to_string()));
    assert!(!names.contains(&LOCATED_IN.to_string()));
}

// ---------------------------------------------------------------
// The merge, and the writes it feeds
// ---------------------------------------------------------------

#[test]
fn two_devices_merge_to_the_best_of_both() {
    let phone = record(&[
        ("best_depth", Value::Number(7)),
        ("runs", Value::Number(12)),
    ]);
    let tablet = record(&[
        ("best_depth", Value::Number(4)),
        ("unlocked_bow", Value::Flag(true)),
    ]);
    let got = merge(&schema(1), &phone, &tablet).expect("both fit the schema");
    assert_eq!(got.number("best_depth"), Some(7));
    assert_eq!(got.number("runs"), Some(12));
    assert!(got.flag("unlocked_bow"));
    // The unlock the tablet earned is not lost, and the depth the
    // phone reached is not lost.
    assert_eq!(got.len(), 3);
}

#[test]
fn a_run_that_ends_worse_writes_nothing() {
    let mut w = world();
    let wrote = save(&mut w, 2, &record(&[("best_depth", Value::Number(7))]));
    assert_eq!(wrote, 1);
    let wrote = save(&mut w, 3, &record(&[("best_depth", Value::Number(3))]));
    assert_eq!(wrote, 0, "a worse run writes nothing");
    assert_eq!(w.record(RUNNER).number("best_depth"), Some(7));
    let wrote = save(&mut w, 4, &record(&[("best_depth", Value::Number(11))]));
    assert_eq!(wrote, 1);
    assert_eq!(w.record(RUNNER).number("best_depth"), Some(11));
    assert!(verify(&w));
}

#[test]
fn the_writes_of_a_record_only_move_forward() {
    let mut w = world();
    save(&mut w, 2, &record(&[("best_depth", Value::Number(7))]));
    let want = record(&[
        ("best_depth", Value::Number(9)),
        ("unlocked_bow", Value::Flag(true)),
    ]);
    let events = writes(&w, RUNNER, &want);
    assert_eq!(events.len(), 2);
    // A start for what is new, a change for what moved, and never
    // an end.
    assert!(events
        .iter()
        .all(|e| !matches!(e, EventKind::FactEnd { .. })));
    assert!(events
        .iter()
        .any(|e| matches!(e, EventKind::FactUpdate { from: 7, to: 9, .. })));
}

#[test]
fn a_backward_write_is_refused_at_the_gate_too() {
    // A server that forgets to merge first still cannot lose the
    // memory of a kid. The gate is the second line of defence.
    let mut w = world();
    save(&mut w, 2, &record(&[("best_depth", Value::Number(7))]));
    let events = writes(&w, RUNNER, &record(&[("best_depth", Value::Number(3))]));
    assert_eq!(events.len(), 1);
    let faults = w
        .propose(Tick(3), events[0].clone())
        .expect_err("a backward write is refused");
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::Backward {
            name: "best_depth".to_string(),
            direction: Direction::Up,
            from: Some(7),
            to: Some(3),
        })]
    );
    assert_eq!(w.record(RUNNER).number("best_depth"), Some(7));
}

// ---------------------------------------------------------------
// The schema grows
// ---------------------------------------------------------------

#[test]
fn the_schema_grows_and_every_old_record_still_fits() {
    let old = record(&[
        ("best_depth", Value::Number(7)),
        ("unlocked_bow", Value::Flag(true)),
    ]);
    assert!(migrate(&schema(1), &schema_v2()).is_empty());
    let got = upgrade(&schema(1), &schema_v2(), &old).expect("an old record carries forward");
    // A new name needs no default, because a missing key IS the
    // start of the join.
    assert_eq!(got, old);
    assert!(got.number("best_gold").is_none());
    // And the new name merges from nothing on the first run.
    let run = record(&[("best_gold", Value::Number(120))]);
    let merged = merge(&schema_v2(), &got, &run).expect("both fit");
    assert_eq!(merged.number("best_gold"), Some(120));
    assert_eq!(merged.number("best_depth"), Some(7));
}

#[test]
fn a_band_that_widens_is_the_one_change_a_name_takes() {
    let mut wider = schema(2);
    wider.declare(
        "best_depth",
        FactRules::solo(Shape::number(Band::new(0, 200)).moving(Direction::Up)),
    );
    assert!(migrate(&schema(1), &wider).is_empty());
    // And a record written under the old band still fits.
    let old = record(&[("best_depth", Value::Number(60))]);
    assert!(upgrade(&schema(1), &wider, &old).is_ok());
}

#[test]
fn a_dropped_name_and_a_narrowed_band_and_new_rules_are_refused() {
    let bare = FactVocabulary::new(2);
    let faults = migrate(&schema(1), &bare);
    assert_eq!(faults.len(), 3);
    assert!(faults.iter().all(|f| matches!(
        f,
        Rejection::Contradiction(Contradiction::NoMigrationPath {
            why: Migration::DroppedName,
            ..
        })
    )));

    let mut narrow = schema(2);
    narrow.declare(
        "best_depth",
        FactRules::solo(Shape::number(Band::new(0, 20)).moving(Direction::Up)),
    );
    assert_eq!(
        migrate(&schema(1), &narrow),
        vec![Rejection::Contradiction(Contradiction::NoMigrationPath {
            name: "best_depth".to_string(),
            why: Migration::BandNarrowed {
                was: (0, 60),
                now: (0, 20),
            },
        })]
    );

    // A direction that changes folds an old history into a new
    // state, so it is refused.
    let mut turned = schema(2);
    turned.declare(
        "best_depth",
        FactRules::solo(Shape::number(Band::new(0, 60)).moving(Direction::Free)),
    );
    assert_eq!(
        migrate(&schema(1), &turned),
        vec![Rejection::Contradiction(Contradiction::NoMigrationPath {
            name: "best_depth".to_string(),
            why: Migration::RulesChanged,
        })]
    );
}

#[test]
fn the_version_steps_by_one_over_a_change_and_holds_still_over_none() {
    // A change with no step.
    let mut same_version = schema_v2();
    same_version.version = 1;
    assert_eq!(
        migrate(&schema(1), &same_version),
        vec![Rejection::Contradiction(Contradiction::VersionStep {
            from: 1,
            to: 1,
            schema_changed: true,
        })]
    );
    // A step with no change.
    assert!(schema_changed(&schema(1), &schema_v2()));
    assert!(!schema_changed(&schema(1), &schema(9)));
    assert_eq!(
        migrate(&schema(1), &schema(2)),
        vec![Rejection::Contradiction(Contradiction::VersionStep {
            from: 1,
            to: 2,
            schema_changed: false,
        })]
    );
    // A step over a change.
    assert!(migrate(&schema(1), &schema_v2()).is_empty());
}
