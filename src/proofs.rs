//! The Kani harnesses. Each one states a law as a bounded proof
//! over whole numbers. No float reaches the solver, because the
//! crate holds none.
//!
//! Each harness proves ONE STEP. A merge of many records is a
//! chain of two-record merges, and a history is a chain of one
//! event, so a proof of the step carries to the whole by
//! induction. No harness unrolls a world.
//!
//! Run with `cargo kani` inside the crate. The harnesses compile
//! only under `cfg(kani)`, so the normal build never sees them.

use crate::fact::{Band, Count, Direction};
use crate::memory::{Join, Value};
use crate::time::{Tick, TimeSpan};

/// The merge law, one field, one step: the join of two numbers
/// is commutative.
#[kani::proof]
fn the_join_answers_the_same_either_way() {
    let x: i64 = kani::any();
    let y: i64 = kani::any();
    let a = Value::Number(x);
    let b = Value::Number(y);
    assert!(Join::Larger.of(a, b) == Join::Larger.of(b, a));
    assert!(Join::Smaller.of(a, b) == Join::Smaller.of(b, a));
}

/// The merge law, one field: the join is associative, so the
/// grouping of three records never changes the answer.
#[kani::proof]
fn the_join_ignores_the_grouping() {
    let x: i64 = kani::any();
    let y: i64 = kani::any();
    let z: i64 = kani::any();
    let a = Value::Number(x);
    let b = Value::Number(y);
    let c = Value::Number(z);
    let left = Join::Larger.of(Join::Larger.of(a, b), c);
    let right = Join::Larger.of(a, Join::Larger.of(b, c));
    assert!(left == right);
    let left = Join::Smaller.of(Join::Smaller.of(a, b), c);
    let right = Join::Smaller.of(a, Join::Smaller.of(b, c));
    assert!(left == right);
}

/// The merge law, one field: the join is idempotent, so a merge
/// that runs twice answers what it answered once.
#[kani::proof]
fn the_join_of_one_record_with_itself_is_that_record() {
    let x: i64 = kani::any();
    let a = Value::Number(x);
    assert!(Join::Larger.of(a, a) == a);
    assert!(Join::Smaller.of(a, a) == a);
    assert!(Join::Larger.of(Join::Larger.of(a, a), a) == a);
}

/// The merge law, one field: the join never moves backward. The
/// answer stands at or past both sides, in the direction of the
/// name.
#[kani::proof]
fn the_join_never_moves_backward() {
    let x: i64 = kani::any();
    let y: i64 = kani::any();
    let up = Join::Larger.of(Value::Number(x), Value::Number(y));
    let down = Join::Smaller.of(Value::Number(x), Value::Number(y));
    match up {
        Value::Number(n) => assert!(n >= x && n >= y),
        Value::Flag(_) => assert!(false),
    }
    match down {
        Value::Number(n) => assert!(n <= x && n <= y),
        Value::Flag(_) => assert!(false),
    }
}

/// The band holds the join. Two numbers inside a band join to a
/// number inside the same band, so a merge never breaks a band
/// and never needs a clamp.
#[kani::proof]
fn the_join_of_two_numbers_in_a_band_stays_in_the_band() {
    let min: i64 = kani::any();
    let max: i64 = kani::any();
    let x: i64 = kani::any();
    let y: i64 = kani::any();
    kani::assume(min <= max);
    let band = Band::new(min, max);
    kani::assume(band.holds(x) && band.holds(y));
    match Join::Larger.of(Value::Number(x), Value::Number(y)) {
        Value::Number(n) => assert!(band.holds(n)),
        Value::Flag(_) => assert!(false),
    }
    match Join::Smaller.of(Value::Number(x), Value::Number(y)) {
        Value::Number(n) => assert!(band.holds(n)),
        Value::Flag(_) => assert!(false),
    }
}

/// The clamp lands inside the band, and a second clamp moves
/// nothing.
#[kani::proof]
fn a_number_lands_inside_its_band() {
    let n: i64 = kani::any();
    let min: i64 = kani::any();
    let max: i64 = kani::any();
    kani::assume(min <= max);
    let band = Band::new(min, max);
    let got = band.clamp(n);
    assert!(band.holds(got));
    assert!(band.clamp(got) == got);
    if band.holds(n) {
        assert!(got == n);
    }
}

/// The direction law, one write: a write the direction allows
/// never lowers an up name and never raises a down name. Two
/// writes in a row keep the same order, so a chain of writes
/// keeps it.
#[kani::proof]
fn a_write_the_direction_allows_keeps_the_order() {
    let a: i64 = kani::any();
    let b: i64 = kani::any();
    let c: i64 = kani::any();
    kani::assume(Direction::Up.allows(a, b) && Direction::Up.allows(b, c));
    assert!(c >= a);
    let d: i64 = kani::any();
    let e: i64 = kani::any();
    let g: i64 = kani::any();
    kani::assume(Direction::Down.allows(d, e) && Direction::Down.allows(e, g));
    assert!(g <= d);
}

/// A band that widens keeps every number the old band held, so a
/// migration that widens breaks no record.
#[kani::proof]
fn a_wider_band_holds_every_old_number() {
    let a: i64 = kani::any();
    let b: i64 = kani::any();
    let c: i64 = kani::any();
    let d: i64 = kani::any();
    let n: i64 = kani::any();
    kani::assume(a <= b && c <= d);
    let was = Band::new(a, b);
    let now = Band::new(c, d);
    kani::assume(was.inside(&now));
    kani::assume(was.holds(n));
    assert!(now.holds(n));
}

/// `One` is `AtMost(1)`, so the validator has one path.
#[kani::proof]
fn one_is_at_most_one() {
    assert!(Count::One.limit() == Count::AtMost(1).limit());
    assert!(Count::One.is_single());
    assert!(Count::AtMost(1).is_single());
    let n: u16 = kani::any();
    kani::assume(n > 1);
    assert!(!Count::AtMost(n).is_single());
    assert!(!Count::Many.is_single());
}

/// A span holds its start and not its end, so one tick has one
/// answer.
#[kani::proof]
fn a_span_holds_its_start_and_not_its_end() {
    let from: u64 = kani::any();
    let until: u64 = kani::any();
    let at: u64 = kani::any();
    kani::assume(until >= from);
    let span = TimeSpan::closed(Tick(from), Tick(until));
    assert!(span.sound());
    assert!(!span.holds_at(Tick(until)));
    if at >= from && at < until {
        assert!(span.holds_at(Tick(at)));
    } else {
        assert!(!span.holds_at(Tick(at)));
    }
    let open = TimeSpan::open(Tick(from));
    assert!(open.holds_at(Tick(at)) == (at >= from));
}
