//! What is true of an entity, and the rules for each name (spec
//! decisions 7, 8, 21 to 25, 32, and 33).
//!
//! A fact is a thing that is true of an entity RIGHT NOW. The
//! mill is burned. The treasury holds 4000. Ada is king of
//! Ashford. A fact holds no time of its own: it points at the
//! event that opened it, and that event carries the tick.
//!
//! The vocabulary is CALLER DATA. It maps a name to its rules,
//! and `validate` refuses a name it does not hold. The same list
//! goes into a director prompt, so a closed set goes in and a
//! closed set comes out.
//!
//! # The shape carries the band and the direction
//!
//! Spec decision 23 writes `Solo { numeric: bool }`. A bool says
//! "this takes a number" and says nothing about WHICH numbers or
//! WHICH WAY they move. The memory of a roguelike needs both: a
//! best depth sits between 1 and 60, and it never falls. So the
//! bool grew into [`Shape`], which is the same enum argument one
//! level down: a band on a flag is nonsense, so a flag cannot
//! declare one.

use crate::entity::EntityType;
use crate::names::Names;
use crate::time::{EntityId, EventId};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// The one fact name the crate declares itself, so a consumer
/// never types it and never misspells it (spec decision 32).
pub const LOCATED_IN: &str = "located_in";

/// Is this name `located_in`? The compare is on two `str` values,
/// because Aeneas cannot translate a compare of `String` with `&str`.
pub(crate) fn is_located_in(name: &str) -> bool {
    same_str(name, LOCATED_IN)
}

/// Two `str` values with the same bytes. The verified code compares a
/// `String` with a `&str` through this function (see `is_located_in`).
pub(crate) fn same_str(a: &str, b: &str) -> bool {
    *a == *b
}

/// A whole-number band, closed at both ends. Every number a fact
/// holds sits inside the band of its name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Band {
    pub min: i64,
    pub max: i64,
}

impl Band {
    pub fn new(min: i64, max: i64) -> Self {
        Band { min, max }
    }

    /// Is this number inside the band?
    #[cfg_attr(charon, verify::start_from)]
    pub fn holds(&self, n: i64) -> bool {
        n >= self.min && n <= self.max
    }

    /// An empty band holds no number.
    #[cfg_attr(charon, verify::start_from)]
    pub fn empty(&self) -> bool {
        self.min > self.max
    }

    /// Pull a number into the band. A band with a top below its
    /// floor answers with the floor, so the function is total.
    #[cfg_attr(charon, verify::start_from)]
    pub fn clamp(&self, n: i64) -> i64 {
        if n < self.min {
            self.min
        } else if n > self.max {
            self.max
        } else {
            n
        }
    }

    /// Does this band sit inside the other one?
    #[cfg_attr(charon, verify::start_from)]
    pub fn inside(&self, other: &Band) -> bool {
        self.min >= other.min && self.max <= other.max
    }
}

/// Which way a value is allowed to move.
///
/// The direction is a LAW, not a hint. `Up` is the law of a
/// memory: a best depth never falls, and an unlock never returns.
/// `Free` is the law of a world: a mill burns, and a mill is
/// rebuilt.
///
/// The direction rules the life of the fact as well as its
/// number. Ending an `Up` fact loses what it remembers, and that
/// is the largest backward write there is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Direction {
    /// The number only rises, and the fact never ends.
    Up,
    /// The number only falls. The fact ends once, and it never
    /// starts again. A flag under `Down` has one life.
    Down,
    /// The number moves either way. The fact ends and starts as
    /// often as the story says.
    Free,
}

impl Direction {
    /// Does a move from `from` to `to` obey the direction?
    #[cfg_attr(charon, verify::start_from)]
    pub fn allows(&self, from: i64, to: i64) -> bool {
        match self {
            Direction::Up => to >= from,
            Direction::Down => to <= from,
            Direction::Free => true,
        }
    }

    /// Can a fact under this direction leave the state? An `Up`
    /// fact never ends, because ending it loses what it
    /// remembers. A `Down` fact ends, and that is the end of it.
    #[cfg_attr(charon, verify::start_from)]
    pub fn can_end(&self) -> bool {
        !matches!(self, Direction::Up)
    }

    /// Can a fact under this direction start again after it
    /// ended? Only a free one. A `Down` flag has one life: a
    /// bridge burns once.
    #[cfg_attr(charon, verify::start_from)]
    pub fn can_restart(&self) -> bool {
        matches!(self, Direction::Free)
    }

    /// The word a rejection carries.
    pub fn label(&self) -> &'static str {
        match self {
            Direction::Up => "up",
            Direction::Down => "down",
            Direction::Free => "free",
        }
    }
}

/// What one fact name carries: a flag, or a number in a band.
/// Both carry a direction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Shape {
    /// True or it is absent. `burned` is `Free`. An unlock is
    /// `Up`, because a kid never loses one.
    Flag { direction: Direction },
    /// A whole number inside a band. A treasury is `Free`. A best
    /// depth is `Up`.
    Number { band: Band, direction: Direction },
}

impl Shape {
    /// A flag that can end.
    pub fn flag() -> Shape {
        Shape::Flag {
            direction: Direction::Free,
        }
    }

    /// A number that moves either way.
    pub fn number(band: Band) -> Shape {
        Shape::Number {
            band,
            direction: Direction::Free,
        }
    }

    /// The same shape, with a direction.
    #[cfg_attr(charon, verify::start_from)]
    pub fn moving(self, direction: Direction) -> Shape {
        match self {
            Shape::Flag { .. } => Shape::Flag { direction },
            Shape::Number { band, .. } => Shape::Number { band, direction },
        }
    }

    #[cfg_attr(charon, verify::start_from)]
    pub fn direction(&self) -> Direction {
        match self {
            Shape::Flag { direction } => *direction,
            Shape::Number { direction, .. } => *direction,
        }
    }

    #[cfg_attr(charon, verify::start_from)]
    pub fn band(&self) -> Option<Band> {
        match self {
            Shape::Flag { .. } => None,
            Shape::Number { band, .. } => Some(*band),
        }
    }

    #[cfg_attr(charon, verify::start_from)]
    pub fn numeric(&self) -> bool {
        matches!(self, Shape::Number { .. })
    }

    pub fn label(&self) -> &'static str {
        match self {
            Shape::Flag { .. } => "a flag",
            Shape::Number { .. } => "a number",
        }
    }
}

/// How many of something one rule allows. `One` is `AtMost(1)`,
/// spelled for the reader (spec decision 25).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Count {
    One,
    Many,
    AtMost(u16),
}

impl Count {
    /// The cap, or nothing when the count is unlimited.
    #[cfg_attr(charon, verify::start_from)]
    pub fn limit(self) -> Option<u16> {
        match self {
            Count::One => Some(1),
            Count::AtMost(n) => Some(n),
            Count::Many => None,
        }
    }

    /// A cap of exactly one. A new fact of that name replaces the
    /// old one, because there is only one thing it can replace
    /// (spec decision 32, the move).
    #[cfg_attr(charon, verify::start_from)]
    pub fn is_single(self) -> bool {
        self.limit() == Some(1)
    }
}

/// The rules for one name. An enum, so a rule about a target
/// cannot be declared on a name that has none.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FactRules {
    /// One sided. `burned`, `treasury`, `best_depth`.
    Solo(Shape),
    /// Two sided. `king_of`, `hates`, `located_in`.
    Linked {
        shape: Shape,
        /// How many entities hold this about one target.
        holders: Count,
        /// How many targets one entity holds it about.
        targets: Count,
        /// Holder type => the target types it allows. Empty means
        /// any (spec decision 33).
        allowed: BTreeMap<EntityType, Vec<EntityType>>,
    },
}

impl FactRules {
    pub fn solo(shape: Shape) -> FactRules {
        FactRules::Solo(shape)
    }

    pub fn linked(shape: Shape, holders: Count, targets: Count) -> FactRules {
        FactRules::Linked {
            shape,
            holders,
            targets,
            allowed: BTreeMap::new(),
        }
    }

    /// Add one line of the type map: this holder type, these
    /// target types.
    pub fn allowing(mut self, holder: EntityType, targets: &[EntityType]) -> FactRules {
        if let FactRules::Linked {
            allowed: ref mut map,
            ..
        } = self
        {
            map.insert(holder, targets.to_vec());
        }
        self
    }

    pub fn shape(&self) -> Shape {
        match self {
            FactRules::Solo(shape) => *shape,
            FactRules::Linked { shape, .. } => *shape,
        }
    }

    pub fn takes_target(&self) -> bool {
        matches!(self, FactRules::Linked { .. })
    }

    /// Does this holder type reach that target type? An empty map
    /// allows any pair.
    pub fn type_allowed(&self, holder: EntityType, target: EntityType) -> bool {
        match self {
            FactRules::Solo(_) => false,
            FactRules::Linked { allowed, .. } => {
                if allowed.is_empty() {
                    return true;
                }
                match allowed.get(&holder) {
                    None => false,
                    Some(list) => holds_type(list, target),
                }
            }
        }
    }

    /// Do two declarations of one name agree on everything that
    /// changes how `apply` folds an event? A migration widens a
    /// band, and it changes nothing else (see `migrate`).
    pub fn same_fold(&self, other: &FactRules) -> bool {
        match (self, other) {
            (FactRules::Solo(a), FactRules::Solo(b)) => shape_same_fold(a, b),
            (
                FactRules::Linked {
                    shape: a,
                    holders: ha,
                    targets: ta,
                    allowed: aa,
                },
                FactRules::Linked {
                    shape: b,
                    holders: hb,
                    targets: tb,
                    allowed: ab,
                },
            ) => shape_same_fold(a, b) && ha == hb && ta == tb && aa == ab,
            _ => false,
        }
    }
}

fn shape_same_fold(a: &Shape, b: &Shape) -> bool {
    match (a, b) {
        (Shape::Flag { direction: x }, Shape::Flag { direction: y }) => x == y,
        (Shape::Number { direction: x, .. }, Shape::Number { direction: y, .. }) => x == y,
        _ => false,
    }
}

/// A thing that is true of an entity right now.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Fact {
    /// Checked against the vocabulary. Never a free string.
    pub name: String,
    /// A number, when the name takes one.
    pub value: Option<i64>,
    /// The second entity, when the name takes one.
    pub linked_to: Option<EntityId>,
    /// The event that made this true. That event carries the tick
    /// and the reason, so a fact stores no time of its own.
    pub opened: EventId,
}

impl Fact {
    /// Do two facts fill the same slot? A slot is the name and
    /// the target together, so Ada hates Bren and Ada hates Cole
    /// are two facts, and neither one closes the other.
    pub fn same_slot(&self, name: &str, linked_to: Option<EntityId>) -> bool {
        self.name == name && self.linked_to == linked_to
    }
}

/// Every fact name one world knows, and the rules for each.
///
/// The vocabulary carries a version. A migration steps it by one
/// (see `migrate`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactVocabulary {
    pub version: u32,
    names: Names<FactRules>,
}

impl Default for FactVocabulary {
    fn default() -> Self {
        FactVocabulary::new(1)
    }
}

impl FactVocabulary {
    /// A new vocabulary already holds `located_in`, so every world
    /// can say where a thing is (spec decision 32).
    pub fn new(version: u32) -> Self {
        let mut names = Names::new();
        names.insert(LOCATED_IN.to_string(), located_in_rules());
        FactVocabulary { version, names }
    }

    /// Declare one name. A second declaration of one name
    /// replaces the first, so a caller cannot hold two.
    pub fn declare(&mut self, name: &str, rules: FactRules) -> &mut Self {
        self.names.insert(name.to_string(), rules);
        self
    }

    pub fn rules(&self, name: &str) -> Option<&FactRules> {
        self.names.get(name)
    }

    /// `rules`, for the verified code (see `names.rs`).
    #[allow(clippy::ptr_arg)]
    pub(crate) fn rules_key(&self, name: &String) -> Option<&FactRules> {
        self.names.get_key(name)
    }

    pub fn holds(&self, name: &str) -> bool {
        self.names.contains(name)
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    /// Every name, in one order on every machine.
    pub fn names(&self) -> impl Iterator<Item = (&String, &FactRules)> {
        self.names.iter()
    }

    /// The vocabulary as rows a prompt can carry (spec decision
    /// 34). The rows are DATA. The consumer writes the sentence,
    /// because Sandcastle talks to a nine-year-old and a game
    /// server talks in a fantasy register (spec decision 27).
    pub fn describe(&self) -> Vec<FactLine> {
        self.names
            .iter()
            .map(|(name, rules)| FactLine {
                name: name.clone(),
                shape: rules.shape(),
                takes_target: rules.takes_target(),
                holders: match rules {
                    FactRules::Linked { holders, .. } => Some(*holders),
                    FactRules::Solo(_) => None,
                },
                targets: match rules {
                    FactRules::Linked { targets, .. } => Some(*targets),
                    FactRules::Solo(_) => None,
                },
                allowed: match rules {
                    FactRules::Linked { allowed, .. } => allowed.clone(),
                    FactRules::Solo(_) => BTreeMap::new(),
                },
            })
            .collect()
    }
}

/// The rules of `located_in`. The crate declares them, so no
/// consumer can weaken them.
pub fn located_in_rules() -> FactRules {
    FactRules::linked(Shape::flag(), Count::Many, Count::One)
        .allowing(EntityType::Person, &[EntityType::Place])
        .allowing(EntityType::Thing, &[EntityType::Person, EntityType::Place])
        .allowing(EntityType::Place, &[EntityType::Place])
        .allowing(EntityType::Faction, &[EntityType::Place])
}

/// Is the type in the list?
fn holds_type(list: &[EntityType], t: EntityType) -> bool {
    let mut i = 0;
    while i < list.len() {
        if list[i] == t {
            return true;
        }
        i += 1;
    }
    false
}

/// One row of the vocabulary, for a prompt. No prose.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactLine {
    pub name: String,
    pub shape: Shape,
    pub takes_target: bool,
    pub holders: Option<Count>,
    pub targets: Option<Count>,
    pub allowed: BTreeMap<EntityType, Vec<EntityType>>,
}

/// The contract of the Lean model of the type map
/// (`lean/Hourglass/TypesExternal.lean`): a list of entries in key
/// order, where `get` is the first entry with an equal key.
#[cfg(test)]
mod tests {
    use super::{Count, EntityType, FactRules, Shape};
    use proptest::prelude::*;

    fn ty() -> impl Strategy<Value = EntityType> {
        prop::sample::select(vec![
            EntityType::Person,
            EntityType::Place,
            EntityType::Thing,
            EntityType::Faction,
        ])
    }

    proptest! {
        /// `type_allowed` answers what the list model answers.
        #[test]
        fn type_allowed_follows_the_model(
            lines in prop::collection::vec((ty(), prop::collection::vec(ty(), 0..4)), 0..6),
            holder in ty(),
            target in ty(),
        ) {
            let mut rules = FactRules::linked(Shape::flag(), Count::Many, Count::Many);
            for (h, ts) in &lines {
                rules = rules.allowing(*h, ts);
            }
            let FactRules::Linked { allowed, .. } = &rules else {
                unreachable!("linked rules");
            };
            let entries: Vec<(EntityType, Vec<EntityType>)> =
                allowed.iter().map(|(k, v)| (*k, v.clone())).collect();
            // The keys are unique and in the order of the derive.
            prop_assert!(entries.windows(2).all(|p| p[0].0 < p[1].0));
            let want = entries.is_empty()
                || match entries.iter().find(|(k, _)| *k == holder) {
                    None => false,
                    Some((_, list)) => list.contains(&target),
                };
            prop_assert_eq!(rules.type_allowed(holder, target), want);
        }
    }
}
