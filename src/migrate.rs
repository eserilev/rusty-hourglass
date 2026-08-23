//! The schema grows (the clepsydra pattern, one version at a
//! time).
//!
//! A game gains a new unlock, a new counter, a new depth. The
//! schema must grow, and every record already on a device must
//! keep its meaning. Three laws hold that:
//!
//! 1. **Additive only.** A new schema drops no name.
//! 2. **The rules of a declared name never change.** A band
//!    WIDENS, and nothing else moves.
//! 3. **The version steps by one over a change, and it holds
//!    still over no change.**
//!
//! Law 2 is not a taste. `apply` reads the rules of a name when
//! it folds an event: the count on the target side decides
//! whether a start closes another fact. Change that, and an old
//! history folds into a NEW state, and the history and the state
//! drift apart. `replay` runs no validation, so nothing
//! catches it. The frozen rules are what make the trust in the log
//! safe.
//!
//! A widened band is the one safe change. Every number the world
//! already holds sits inside the wider band, and `apply` never
//! reads a band.
//!
//! A new name needs no default. A missing key IS the start of the
//! join (see `memory`), so nothing has to be filled in.

use crate::fact::FactVocabulary;
use crate::memory::{check, Record};
use crate::reject::{Contradiction, Migration, Rejection};

/// Does the schema differ between the two versions?
pub fn schema_changed(previous: &FactVocabulary, next: &FactVocabulary) -> bool {
    if previous.len() != next.len() {
        return true;
    }
    for (name, was) in previous.names() {
        match next.rules(name) {
            None => return true,
            Some(now) => {
                if was != now {
                    return true;
                }
            }
        }
    }
    false
}

/// Run the three laws. Every reason comes back at once.
pub fn migrate(previous: &FactVocabulary, next: &FactVocabulary) -> Vec<Rejection> {
    let mut out = Vec::new();
    for (name, was) in previous.names() {
        let Some(now) = next.rules(name) else {
            out.push(Rejection::Contradiction(Contradiction::NoMigrationPath {
                name: name.clone(),
                why: Migration::DroppedName,
            }));
            continue;
        };
        if !was.same_fold(now) {
            out.push(Rejection::Contradiction(Contradiction::NoMigrationPath {
                name: name.clone(),
                why: Migration::RulesChanged,
            }));
            continue;
        }
        if let (Some(before), Some(after)) = (was.shape().band(), now.shape().band()) {
            if !before.inside(&after) {
                out.push(Rejection::Contradiction(Contradiction::NoMigrationPath {
                    name: name.clone(),
                    why: Migration::BandNarrowed {
                        was: (before.min, before.max),
                        now: (after.min, after.max),
                    },
                }));
            }
        }
    }
    let changed = schema_changed(previous, next);
    let want = if changed {
        previous.version.saturating_add(1)
    } else {
        previous.version
    };
    if next.version != want {
        out.push(Rejection::Contradiction(Contradiction::VersionStep {
            from: previous.version,
            to: next.version,
            schema_changed: changed,
        }));
    }
    out
}

/// Carry one record from the old schema to the new one.
///
/// The record comes back unchanged. That is the whole claim of an
/// additive migration: when the three laws pass, no record on any
/// device needs a rewrite, and none of them breaks the new
/// schema.
pub fn upgrade(
    previous: &FactVocabulary,
    next: &FactVocabulary,
    record: &Record,
) -> Result<Record, Vec<Rejection>> {
    let mut faults = migrate(previous, next);
    faults.extend(check(next, record));
    if faults.is_empty() {
        Ok(record.clone())
    } else {
        Err(faults)
    }
}
