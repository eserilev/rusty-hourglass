//! Build steps 1 to 3: the types, `apply` and `replay`, and the
//! containment queries.

use hourglass::*;

/// The vocabulary of a dungeon. It is caller data, and the crate
/// holds no word of it.
pub fn dungeon() -> FactVocabulary {
    let mut v = FactVocabulary::new(1);
    v.declare(
        "best_depth",
        FactRules::solo(Shape::number(Band::new(0, 60)).moving(Direction::Up)),
    );
    v.declare(
        "runs",
        FactRules::solo(Shape::number(Band::new(0, 100_000)).moving(Direction::Up)),
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
        FactRules::linked(Shape::flag(), Count::AtMost(3), Count::Many)
            .allowing(EntityType::Person, &[EntityType::Place]),
    );
    v
}

pub const ADA: EntityId = EntityId(0);
pub const ASHFORD: EntityId = EntityId(1);
pub const MILL: EntityId = EntityId(2);
pub const BREN: EntityId = EntityId(3);

/// Ada, Ashford, the mill, and Bren. Nothing is placed yet.
pub fn cast() -> World {
    let mut w = World::new(dungeon());
    let people = [
        (ADA, EntityType::Person, "Ada"),
        (ASHFORD, EntityType::Place, "Ashford"),
        (MILL, EntityType::Place, "the mill"),
        (BREN, EntityType::Person, "Bren"),
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

fn place(w: &mut World, tick: u64, who: EntityId, at: EntityId) {
    w.propose(
        Tick(tick),
        EventKind::FactStart {
            entity: who,
            name: LOCATED_IN.to_string(),
            value: None,
            linked_to: Some(at),
        },
    )
    .expect("the move is legal");
}

// ---------------------------------------------------------------
// Step 1: the types
// ---------------------------------------------------------------

#[test]
fn every_type_round_trips_through_json() {
    let mut w = cast();
    place(&mut w, 2, MILL, ASHFORD);
    place(&mut w, 2, ADA, MILL);
    w.propose(
        Tick(3),
        EventKind::FactStart {
            entity: ASHFORD,
            name: "treasury".to_string(),
            value: Some(4000),
            linked_to: None,
        },
    )
    .expect("a treasury is legal");

    let text = serde_json::to_string(&w).expect("a world writes as json");
    let back: World = serde_json::from_str(&text).expect("a world reads back");
    assert_eq!(w, back);

    let brief = w.brief(Some(ADA), Budget::new(3, 2));
    let text = serde_json::to_string(&brief).expect("a briefing writes as json");
    let back: Briefing = serde_json::from_str(&text).expect("a briefing reads back");
    assert_eq!(brief, back);

    let span = TimeSpan::closed(Tick(12), Tick(50));
    let back: TimeSpan =
        serde_json::from_str(&serde_json::to_string(&span).unwrap()).expect("a span reads back");
    assert_eq!(span, back);
}

#[test]
fn a_vocabulary_answers_a_declared_name_and_nothing_else() {
    let v = dungeon();
    assert!(v.rules("best_depth").is_some());
    assert!(v.rules("best depth").is_none());
    assert!(v.rules("treasure").is_none());
    assert_eq!(
        v.rules("best_depth").map(|r| r.shape().band()),
        Some(Some(Band::new(0, 60)))
    );
}

#[test]
fn a_new_vocabulary_already_holds_located_in() {
    let v = FactVocabulary::new(1);
    assert!(v.holds(LOCATED_IN));
    assert_eq!(v.len(), 1);
    let rules = v.rules(LOCATED_IN).expect("the crate declares it");
    assert!(rules.takes_target());
    assert!(rules.type_allowed(EntityType::Person, EntityType::Place));
    assert!(!rules.type_allowed(EntityType::Person, EntityType::Person));
}

#[test]
fn a_span_answers_before_during_and_after() {
    let span = TimeSpan::closed(Tick(12), Tick(50));
    assert!(!span.holds_at(Tick(11)));
    assert!(span.holds_at(Tick(12)));
    assert!(span.holds_at(Tick(49)));
    assert!(!span.holds_at(Tick(50)));
    assert!(span.ended());
    assert!(span.sound());
    let open = TimeSpan::open(Tick(12));
    assert!(open.holds_at(Tick(9_000)));
    assert!(!open.ended());
}

#[test]
fn the_vocabulary_describes_itself_for_a_prompt() {
    let lines = dungeon().describe();
    let king = lines
        .iter()
        .find(|l| l.name == "king_of")
        .expect("king_of is declared");
    assert!(king.takes_target);
    assert_eq!(king.holders, Some(Count::One));
    assert_eq!(king.targets, Some(Count::Many));
    assert_eq!(
        king.allowed.get(&EntityType::Person),
        Some(&vec![EntityType::Place])
    );
    let depth = lines
        .iter()
        .find(|l| l.name == "best_depth")
        .expect("best_depth is declared");
    assert!(!depth.takes_target);
    assert_eq!(depth.shape.direction(), Direction::Up);
    // The rows are data. No sentence lives in the crate.
    assert_eq!(lines.len(), dungeon().len());
}

// ---------------------------------------------------------------
// Step 2: apply and replay
// ---------------------------------------------------------------

#[test]
fn the_same_history_builds_the_same_state() {
    let mut w = cast();
    place(&mut w, 2, MILL, ASHFORD);
    place(&mut w, 2, ADA, MILL);
    w.propose(
        Tick(3),
        EventKind::FactStart {
            entity: ADA,
            name: "king_of".to_string(),
            value: None,
            linked_to: Some(ASHFORD),
        },
    )
    .expect("one king is legal");

    let once = World::replay(dungeon(), w.history());
    let twice = World::replay(dungeon(), w.history());
    assert_eq!(once, twice);
    assert_eq!(once, w);
    assert!(verify(&w));
}

#[test]
fn a_fact_that_ends_leaves_the_state_and_the_history_keeps_it() {
    let mut w = cast();
    w.propose(
        Tick(51),
        EventKind::FactStart {
            entity: MILL,
            name: "burned".to_string(),
            value: None,
            linked_to: None,
        },
    )
    .expect("a fire is legal");
    assert!(w.entity(MILL).expect("the mill is here").has("burned"));

    w.propose(
        Tick(58),
        EventKind::FactEnd {
            entity: MILL,
            name: "burned".to_string(),
            linked_to: None,
        },
    )
    .expect("a repair is legal");
    assert!(!w.entity(MILL).expect("the mill is here").has("burned"));
    // The history holds both, so "the mill burned in 51 and was
    // rebuilt in 58" still answers.
    assert_eq!(w.history().len(), 6);
    assert!(w.ever_ended(MILL, "burned"));
    assert!(verify(&w));
}

#[test]
fn a_number_change_closes_the_old_value_and_opens_the_new() {
    let mut w = cast();
    let opened = w
        .propose(
            Tick(3),
            EventKind::FactStart {
                entity: ASHFORD,
                name: "treasury".to_string(),
                value: Some(4000),
                linked_to: None,
            },
        )
        .expect("a treasury is legal");
    let changed = w
        .propose(
            Tick(40),
            EventKind::FactUpdate {
                entity: ASHFORD,
                name: "treasury".to_string(),
                linked_to: None,
                from: 4000,
                to: 900,
            },
        )
        .expect("the treasury falls");
    let fact = w
        .entity(ASHFORD)
        .and_then(|e| e.fact("treasury", None))
        .expect("the treasury is here");
    assert_eq!(fact.value, Some(900));
    // A new value is a new fact, so the fact points at the change.
    assert_eq!(fact.opened, changed);
    assert_ne!(fact.opened, opened);
    assert_eq!(w.history().get(changed).map(|e| e.tick), Some(Tick(40)));
    assert!(verify(&w));
}

#[test]
fn an_entity_stays_after_it_dies_with_its_existence_closed() {
    let mut w = cast();
    w.propose(
        Tick(3),
        EventKind::FactStart {
            entity: BREN,
            name: "hates".to_string(),
            value: Some(7),
            linked_to: Some(ADA),
        },
    )
    .expect("a grudge is legal");
    w.propose(Tick(50), EventKind::EntityDestroyed { id: ADA })
        .expect("Ada dies");

    let ada = w.entity(ADA).expect("Ada stays in the state");
    assert!(ada.gone());
    assert_eq!(ada.existence.until, Some(Tick(50)));
    assert!(!ada.existence.holds_at(Tick(50)));
    assert!(ada.existence.holds_at(Tick(49)));
    // A fact does not end because somebody dies. The grudge
    // outlives Ada.
    assert_eq!(w.facts_linked_to(ADA).len(), 1);
    assert!(verify(&w));
}

#[test]
fn one_slot_holds_one_fact_and_two_targets_hold_two() {
    let mut w = cast();
    for (target, value) in [(ADA, 7), (MILL, 2)] {
        w.propose(
            Tick(3),
            EventKind::FactStart {
                entity: BREN,
                name: "hates".to_string(),
                value: Some(value),
                linked_to: Some(target),
            },
        )
        .expect("a grudge is legal");
    }
    // Two targets, so two facts. Neither one closed the other.
    assert_eq!(w.targets_of("hates", BREN).len(), 2);
    // The same slot again replaces, so a mill is not burned twice.
    w.propose(
        Tick(4),
        EventKind::FactStart {
            entity: BREN,
            name: "hates".to_string(),
            value: Some(9),
            linked_to: Some(ADA),
        },
    )
    .expect("a deeper grudge is legal");
    assert_eq!(w.targets_of("hates", BREN).len(), 2);
    assert_eq!(
        w.entity(BREN)
            .and_then(|e| e.fact("hates", Some(ADA)))
            .and_then(|f| f.value),
        Some(9)
    );
    assert!(verify(&w));
}

#[test]
fn the_history_only_grows_and_the_ids_run_in_order() {
    let w = cast();
    assert_eq!(w.history().len(), 4);
    assert_eq!(w.history().next_id(), EventId(4));
    let ids: Vec<u64> = w.history().iter().map(|e| e.id.0).collect();
    assert_eq!(ids, vec![0, 1, 2, 3]);
    assert_eq!(w.history().tail(2).len(), 2);
    assert_eq!(w.history().tail(90).len(), 4);
}

// ---------------------------------------------------------------
// Step 3: located_in and the containment queries
// ---------------------------------------------------------------

#[test]
fn contents_and_ancestry_walk_the_chain() {
    let mut w = cast();
    place(&mut w, 2, MILL, ASHFORD);
    place(&mut w, 2, ADA, MILL);
    assert_eq!(w.contents(MILL), vec![ADA]);
    assert_eq!(w.ancestry(ADA), vec![MILL, ASHFORD]);
    assert_eq!(w.ancestry(ASHFORD), Vec::<EntityId>::new());
    assert!(verify(&w));
}

#[test]
fn a_move_ends_the_old_location_and_opens_the_new() {
    let mut w = cast();
    place(&mut w, 2, ADA, MILL);
    assert_eq!(w.location_of(ADA), Some(MILL));
    place(&mut w, 3, ADA, ASHFORD);
    // One place at a time. The count on the target side is one,
    // so the move closed the old fact and left no choice.
    assert_eq!(w.location_of(ADA), Some(ASHFORD));
    assert_eq!(
        w.entity(ADA).map(|e| e.facts_named(LOCATED_IN).count()),
        Some(1)
    );
    assert_eq!(w.contents(MILL), Vec::<EntityId>::new());
    assert!(verify(&w));
}

// ---------------------------------------------------------------
// Rollback
// ---------------------------------------------------------------

#[test]
fn a_rollback_equals_a_replay_of_the_prefix() {
    let mut w = cast();
    place(&mut w, 2, MILL, ASHFORD);
    let cut = w.history().next_id().0 - 1;
    let before = w.clone();

    place(&mut w, 3, ADA, MILL);
    w.propose(
        Tick(4),
        EventKind::FactStart {
            entity: MILL,
            name: "burned".to_string(),
            value: None,
            linked_to: None,
        },
    )
    .expect("a fire is legal");
    assert_ne!(w, before);

    w.rewind(EventId(cut));
    // The undo of a child: cut the history, and build the state
    // from nothing.
    assert_eq!(w.history().len(), before.history().len());
    assert_eq!(w.entities().count(), before.entities().count());
    assert_eq!(w.location_of(ADA), None);
    assert!(!w.entity(MILL).expect("the mill is here").has("burned"));
    assert_eq!(w, before);
    assert!(verify(&w));
}
