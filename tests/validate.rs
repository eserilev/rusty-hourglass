//! Build step 4: the gate. One test per rejection, each one
//! proving the exact reason, plus the two promises that make a
//! retry cheap.

use hourglass::*;

fn dungeon() -> FactVocabulary {
    let mut v = FactVocabulary::new(1);
    v.declare(
        "best_depth",
        FactRules::solo(Shape::number(Band::new(0, 60)).moving(Direction::Up)),
    );
    v.declare(
        "treasury",
        FactRules::solo(Shape::number(Band::new(0, 100_000))),
    );
    v.declare(
        "unlocked_bow",
        FactRules::solo(Shape::flag().moving(Direction::Up)),
    );
    v.declare("burned", FactRules::solo(Shape::flag()));
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
        FactRules::linked(Shape::flag(), Count::Many, Count::AtMost(3))
            .allowing(EntityType::Person, &[EntityType::Place]),
    );
    v
}

const ADA: EntityId = EntityId(0);
const ASHFORD: EntityId = EntityId(1);
const MILL: EntityId = EntityId(2);
const BREN: EntityId = EntityId(3);
const SWORD: EntityId = EntityId(4);
const ELIN: EntityId = EntityId(5);

fn cast() -> World {
    let mut w = World::new(dungeon());
    let people = [
        (ADA, EntityType::Person, "Ada"),
        (ASHFORD, EntityType::Place, "Ashford"),
        (MILL, EntityType::Place, "the mill"),
        (BREN, EntityType::Person, "Bren"),
        (SWORD, EntityType::Thing, "the sword"),
        (ELIN, EntityType::Person, "Elin"),
    ];
    for (id, entity_type, name) in people {
        w.propose(
            Tick(1),
            EventKind::EntityCreated {
                id,
                entity_type,
                name: name.to_string(),
            },
        )
        .expect("the cast is legal");
    }
    w
}

fn start(
    entity: EntityId,
    name: &str,
    value: Option<i64>,
    linked_to: Option<EntityId>,
) -> EventKind {
    EventKind::FactStart {
        entity,
        name: name.to_string(),
        value,
        linked_to,
    }
}

fn refuse(w: &mut World, kind: EventKind) -> Vec<Rejection> {
    let before = w.history().len();
    let at = w.tick;
    let faults = w.propose(at, kind).expect_err("the event is refused");
    // A refused event never lands, so the history never grows.
    assert_eq!(w.history().len(), before);
    faults
}

// ---------------------------------------------------------------
// Malformed: wrong on its own
// ---------------------------------------------------------------

#[test]
fn an_unknown_fact_name_is_malformed() {
    let mut w = cast();
    let faults = refuse(&mut w, start(MILL, "treasure", None, None));
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::UnknownFact {
            name: "treasure".to_string()
        })]
    );
    assert!(faults[0].malformed());
}

#[test]
fn a_number_name_needs_a_number_and_a_flag_takes_none() {
    let mut w = cast();
    let faults = refuse(&mut w, start(ASHFORD, "treasury", None, None));
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::NeedsNumber {
            name: "treasury".to_string()
        })]
    );
    let faults = refuse(&mut w, start(MILL, "burned", Some(3), None));
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::TakesNoNumber {
            name: "burned".to_string()
        })]
    );
}

#[test]
fn a_linked_name_needs_a_target_and_a_solo_name_takes_none() {
    let mut w = cast();
    let faults = refuse(&mut w, start(ADA, "king_of", None, None));
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::NeedsTarget {
            name: "king_of".to_string()
        })]
    );
    let faults = refuse(&mut w, start(MILL, "burned", None, Some(ASHFORD)));
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::TakesNoTarget {
            name: "burned".to_string()
        })]
    );
}

#[test]
fn a_type_outside_the_map_is_refused() {
    let mut w = cast();
    // A sword cannot be king, and Ada does not live inside Bren.
    let faults = refuse(&mut w, start(SWORD, "king_of", None, Some(ASHFORD)));
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::TypeNotAllowed {
            name: "king_of".to_string(),
            holder: EntityType::Thing,
            target: EntityType::Place,
        })]
    );
    let faults = refuse(&mut w, start(ADA, LOCATED_IN, None, Some(BREN)));
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::TypeNotAllowed {
            name: LOCATED_IN.to_string(),
            holder: EntityType::Person,
            target: EntityType::Person,
        })]
    );
    // A thing goes in a person, so the sword rides with Ada.
    w.propose(Tick(2), start(SWORD, LOCATED_IN, None, Some(ADA)))
        .expect("a thing goes in a person");
}

#[test]
fn a_number_outside_the_band_is_refused() {
    let mut w = cast();
    let faults = refuse(&mut w, start(ADA, "best_depth", Some(61), None));
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::OutOfBand {
            name: "best_depth".to_string(),
            value: 61,
            min: 0,
            max: 60,
        })]
    );
    let faults = refuse(&mut w, start(ADA, "best_depth", Some(-1), None));
    assert!(matches!(
        faults[0],
        Rejection::Malformed(Malformed::OutOfBand { value: -1, .. })
    ));
}

#[test]
fn a_backward_update_is_refused_by_the_vocabulary_alone() {
    let mut w = cast();
    w.propose(Tick(2), start(ADA, "best_depth", Some(7), None))
        .expect("a first dive is legal");
    let faults = w
        .propose(
            Tick(3),
            EventKind::FactUpdate {
                entity: ADA,
                name: "best_depth".to_string(),
                linked_to: None,
                from: 7,
                to: 4,
            },
        )
        .expect_err("a best depth never falls");
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::Backward {
            name: "best_depth".to_string(),
            direction: Direction::Up,
            from: Some(7),
            to: Some(4),
        })]
    );
    // The same write forward lands.
    w.propose(
        Tick(3),
        EventKind::FactUpdate {
            entity: ADA,
            name: "best_depth".to_string(),
            linked_to: None,
            from: 7,
            to: 9,
        },
    )
    .expect("a deeper dive is legal");
    assert_eq!(w.entity(ADA).and_then(|e| e.value("best_depth")), Some(9));
}

#[test]
fn an_up_fact_never_ends() {
    let mut w = cast();
    w.propose(Tick(2), start(ADA, "unlocked_bow", None, None))
        .expect("an unlock is legal");
    let faults = refuse(
        &mut w,
        EventKind::FactEnd {
            entity: ADA,
            name: "unlocked_bow".to_string(),
            linked_to: None,
        },
    );
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::Backward {
            name: "unlocked_bow".to_string(),
            direction: Direction::Up,
            from: None,
            to: None,
        })]
    );
    assert!(w.entity(ADA).expect("Ada is here").has("unlocked_bow"));
}

#[test]
fn an_update_of_a_flag_is_refused() {
    let mut w = cast();
    w.propose(Tick(2), start(MILL, "burned", None, None))
        .expect("a fire is legal");
    let faults = refuse(
        &mut w,
        EventKind::FactUpdate {
            entity: MILL,
            name: "burned".to_string(),
            linked_to: None,
            from: 0,
            to: 1,
        },
    );
    assert!(
        faults.contains(&Rejection::Malformed(Malformed::TakesNoNumber {
            name: "burned".to_string()
        }))
    );
}

#[test]
fn an_entity_with_no_name_is_refused() {
    let mut w = cast();
    let faults = refuse(
        &mut w,
        EventKind::EntityCreated {
            id: EntityId(9),
            entity_type: EntityType::Person,
            name: "  ".to_string(),
        },
    );
    assert_eq!(
        faults,
        vec![Rejection::Malformed(Malformed::UnnamedEntity {
            id: EntityId(9)
        })]
    );
}

// ---------------------------------------------------------------
// Contradiction: the world is in the way
// ---------------------------------------------------------------

#[test]
fn an_unknown_entity_and_a_taken_handle_are_refused() {
    let mut w = cast();
    let faults = refuse(&mut w, start(EntityId(77), "burned", None, None));
    assert_eq!(
        faults,
        vec![Rejection::Contradiction(Contradiction::UnknownEntity {
            id: EntityId(77)
        })]
    );
    let faults = refuse(
        &mut w,
        EventKind::EntityCreated {
            id: ADA,
            entity_type: EntityType::Person,
            name: "another Ada".to_string(),
        },
    );
    assert_eq!(
        faults,
        vec![Rejection::Contradiction(Contradiction::IdInUse { id: ADA })]
    );
}

#[test]
fn a_dead_entity_gains_no_facts() {
    let mut w = cast();
    w.propose(Tick(2), EventKind::EntityDestroyed { id: ADA })
        .expect("Ada dies");
    let faults = refuse(&mut w, start(ADA, "unlocked_bow", None, None));
    assert_eq!(
        faults,
        vec![Rejection::Contradiction(Contradiction::Gone { id: ADA })]
    );
    // And Ada dies once.
    let faults = refuse(&mut w, EventKind::EntityDestroyed { id: ADA });
    assert_eq!(
        faults,
        vec![Rejection::Contradiction(Contradiction::Gone { id: ADA })]
    );
    // A grudge still points at Ada, because the history names the
    // dead.
    w.propose(Tick(2), start(BREN, "hates", Some(7), Some(ADA)))
        .expect("a grudge outlives the person");
}

#[test]
fn an_entity_never_points_at_itself() {
    let mut w = cast();
    let faults = refuse(&mut w, start(ASHFORD, LOCATED_IN, None, Some(ASHFORD)));
    assert!(
        faults.contains(&Rejection::Contradiction(Contradiction::SelfReference {
            id: ASHFORD
        }))
    );
}

#[test]
fn a_ring_of_places_is_refused() {
    let mut w = cast();
    w.propose(Tick(2), start(MILL, LOCATED_IN, None, Some(ASHFORD)))
        .expect("the mill sits in Ashford");
    let faults = refuse(&mut w, start(ASHFORD, LOCATED_IN, None, Some(MILL)));
    assert_eq!(
        faults,
        vec![Rejection::Contradiction(Contradiction::Cycle {
            entity: ASHFORD,
            through: ASHFORD,
        })]
    );
    assert!(verify(&w));
}

/// A walk with a hop cap let this ring through: a chain longer than
/// the cap answered "no cycle". The chain here is longer than 1024.
#[test]
fn a_ring_longer_than_any_cap_is_refused() {
    let mut w = World::new(dungeon());
    let places: Vec<EntityId> = (0..1100).map(EntityId).collect();
    for &id in &places {
        w.propose(
            Tick(1),
            EventKind::EntityCreated {
                id,
                entity_type: EntityType::Place,
                name: format!("place {}", id.0),
            },
        )
        .expect("a new place is legal");
    }
    for pair in places.windows(2) {
        w.propose(Tick(2), start(pair[0], LOCATED_IN, None, Some(pair[1])))
            .expect("a chain of places is legal");
    }
    // A long chain is sound: the referee walks it to the end.
    assert!(verify(&w));
    let last = places[places.len() - 1];
    let faults = refuse(&mut w, start(last, LOCATED_IN, None, Some(places[0])));
    assert_eq!(
        faults,
        vec![Rejection::Contradiction(Contradiction::Cycle {
            entity: last,
            through: last,
        })]
    );
}

#[test]
fn a_second_king_is_refused_and_names_the_first() {
    let mut w = cast();
    w.propose(Tick(2), start(ADA, "king_of", None, Some(ASHFORD)))
        .expect("one king is legal");
    let faults = refuse(&mut w, start(BREN, "king_of", None, Some(ASHFORD)));
    assert_eq!(
        faults,
        vec![Rejection::Contradiction(Contradiction::TooManyHolders {
            name: "king_of".to_string(),
            target: ASHFORD,
            held_by: vec![ADA],
            limit: 1,
        })]
    );
    // The crate says what blocks it. End the crown of Ada, and
    // the retry lands.
    w.propose(
        Tick(3),
        EventKind::FactEnd {
            entity: ADA,
            name: "king_of".to_string(),
            linked_to: Some(ASHFORD),
        },
    )
    .expect("a crown ends");
    w.propose(Tick(3), start(BREN, "king_of", None, Some(ASHFORD)))
        .expect("Bren is crowned");
    // Ada rules two cities, because the target side is many.
    w.propose(Tick(3), start(ADA, "king_of", None, Some(MILL)))
        .expect("a second city is legal");
    assert!(verify(&w));
}

#[test]
fn a_fourth_council_seat_is_refused() {
    let mut w = cast();
    let places = [ASHFORD, MILL];
    for at in places {
        w.propose(Tick(2), start(ADA, "council_of", None, Some(at)))
            .expect("a seat is legal");
    }
    w.propose(
        Tick(2),
        EventKind::EntityCreated {
            id: EntityId(9),
            entity_type: EntityType::Place,
            name: "Bram".to_string(),
        },
    )
    .expect("a third city");
    w.propose(Tick(2), start(ADA, "council_of", None, Some(EntityId(9))))
        .expect("a third seat is legal");
    w.propose(
        Tick(2),
        EventKind::EntityCreated {
            id: EntityId(10),
            entity_type: EntityType::Place,
            name: "Corran".to_string(),
        },
    )
    .expect("a fourth city");
    let faults = refuse(&mut w, start(ADA, "council_of", None, Some(EntityId(10))));
    match &faults[0] {
        Rejection::Contradiction(Contradiction::TooManyTargets {
            name,
            holder,
            pointing_at,
            limit,
        }) => {
            assert_eq!(name, "council_of");
            assert_eq!(*holder, ADA);
            assert_eq!(pointing_at.len(), 3);
            assert_eq!(*limit, 3);
        }
        other => panic!("wrong reason: {other:?}"),
    }
    assert!(verify(&w));
}

#[test]
fn a_stale_update_is_refused_and_a_missing_fact_too() {
    let mut w = cast();
    w.propose(Tick(2), start(ASHFORD, "treasury", Some(4000), None))
        .expect("a treasury is legal");
    w.propose(
        Tick(3),
        EventKind::FactUpdate {
            entity: ASHFORD,
            name: "treasury".to_string(),
            linked_to: None,
            from: 4000,
            to: 900,
        },
    )
    .expect("the treasury falls");
    // A director read the old briefing and thought too long.
    let faults = refuse(
        &mut w,
        EventKind::FactUpdate {
            entity: ASHFORD,
            name: "treasury".to_string(),
            linked_to: None,
            from: 4000,
            to: 3000,
        },
    );
    assert_eq!(
        faults,
        vec![Rejection::Contradiction(Contradiction::Stale {
            entity: ASHFORD,
            name: "treasury".to_string(),
            want: 4000,
            got: 900,
        })]
    );
    let faults = refuse(
        &mut w,
        EventKind::FactUpdate {
            entity: MILL,
            name: "treasury".to_string(),
            linked_to: None,
            from: 0,
            to: 5,
        },
    );
    assert_eq!(
        faults,
        vec![Rejection::Contradiction(Contradiction::NoSuchFact {
            entity: MILL,
            name: "treasury".to_string(),
            linked_to: None,
        })]
    );
}

#[test]
fn a_best_depth_never_starts_again_lower() {
    let mut w = cast();
    w.propose(Tick(2), start(ADA, "best_depth", Some(7), None))
        .expect("a first dive is legal");
    // The loophole a start opens: write the memory again from
    // nothing.
    let faults = refuse(&mut w, start(ADA, "best_depth", Some(0), None));
    assert_eq!(
        faults,
        vec![Rejection::Contradiction(Contradiction::Backward {
            entity: ADA,
            name: "best_depth".to_string(),
            direction: Direction::Up,
            held: Some(7),
            proposed: Some(0),
        })]
    );
    // A deeper dive lands, whichever event writes it.
    w.propose(Tick(3), start(ADA, "best_depth", Some(11), None))
        .expect("a deeper dive is legal");
    assert_eq!(w.entity(ADA).and_then(|e| e.value("best_depth")), Some(11));
    assert!(verify(&w));
}

#[test]
fn a_tick_never_moves_back() {
    let mut w = cast();
    w.propose(Tick(9), start(MILL, "burned", None, None))
        .expect("a fire is legal");
    let faults = w
        .propose(
            Tick(4),
            EventKind::FactEnd {
                entity: MILL,
                name: "burned".to_string(),
                linked_to: None,
            },
        )
        .expect_err("time never moves back");
    assert_eq!(
        faults,
        vec![Rejection::Contradiction(Contradiction::TimeMovedBack {
            was: Tick(9),
            got: Tick(4),
        })]
    );
}

// ---------------------------------------------------------------
// The two promises that make a retry cheap
// ---------------------------------------------------------------

#[test]
fn a_refusal_carries_every_reason_not_the_first() {
    let mut w = cast();
    w.propose(Tick(2), EventKind::EntityDestroyed { id: SWORD })
        .expect("the sword is destroyed");
    // Three faults at once: a dead holder, a number on a flag,
    // and a pair of types the map refuses. A gate that stopped at
    // the first one costs three round trips.
    let faults = refuse(&mut w, start(SWORD, "king_of", Some(3), Some(BREN)));
    assert_eq!(faults.len(), 3, "wanted every reason, got {faults:?}");
    assert!(faults.contains(&Rejection::Contradiction(Contradiction::Gone { id: SWORD })));
    assert!(
        faults.contains(&Rejection::Malformed(Malformed::TakesNoNumber {
            name: "king_of".to_string()
        }))
    );
    assert!(
        faults.contains(&Rejection::Malformed(Malformed::TypeNotAllowed {
            name: "king_of".to_string(),
            holder: EntityType::Thing,
            target: EntityType::Person,
        }))
    );
    // Every reason writes a line of its own, and no line is
    // empty. The consumer words it again.
    for fault in &faults {
        assert!(!fault.to_string().is_empty());
    }
}

#[test]
fn good_events_land_while_bad_ones_are_refused_in_one_tick() {
    let mut w = cast();
    let answers = w.propose_all(
        Tick(4),
        vec![
            start(MILL, "burned", None, None),
            start(ADA, "treasure", Some(1), None),
            start(ADA, "king_of", None, Some(ASHFORD)),
            start(BREN, "king_of", None, Some(ASHFORD)),
            start(ADA, "unlocked_bow", None, None),
        ],
    );
    let landed = answers.iter().filter(|a| a.is_ok()).count();
    assert_eq!(landed, 3);
    assert!(answers[1].is_err());
    assert!(answers[3].is_err());
    // A bad proposal costs one event, never the whole tick.
    assert!(w.entity(MILL).expect("the mill is here").has("burned"));
    assert!(w.entity(ADA).expect("Ada is here").has("unlocked_bow"));
    assert_eq!(w.holders_of("king_of", ASHFORD), vec![ADA]);
    assert!(verify(&w));
}

#[test]
fn the_vocabulary_check_names_a_broken_declaration() {
    let mut v = FactVocabulary::new(1);
    v.declare(
        "depth",
        FactRules::solo(Shape::number(Band::new(60, 0)).moving(Direction::Up)),
    );
    v.declare(
        "seat",
        FactRules::linked(Shape::flag(), Count::AtMost(0), Count::Many),
    );
    v.declare(LOCATED_IN, FactRules::solo(Shape::flag()));
    let faults = vocabulary_sound(&v);
    assert_eq!(faults.len(), 3, "wanted three faults, got {faults:?}");
    assert!(faults.iter().all(|f| f.malformed()));
    let sound = FactVocabulary::new(1);
    assert!(vocabulary_sound(&sound).is_empty());
}
