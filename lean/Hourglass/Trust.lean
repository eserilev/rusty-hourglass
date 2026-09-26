-- The trust check. Each law depends only on the three standard axioms
-- of Lean. A `sorry` or a new axiom changes the output, and the build fails.
import Hourglass.Laws
import Hourglass.Merge
import Hourglass.World
import Hourglass.Apply
import Hourglass.Gate
import Hourglass.Direction

open hourglass

/-- info: 'hourglass.join_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms join_comm

/-- info: 'hourglass.join_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms join_assoc

/-- info: 'hourglass.join_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms join_idem

/-- info: 'hourglass.join_never_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms join_never_backward

/-- info: 'hourglass.join_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms join_total

/-- info: 'hourglass.join_stays_in_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms join_stays_in_band

/-- info: 'hourglass.clamp_lands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clamp_lands

/-- info: 'hourglass.wider_band_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wider_band_holds

/-- info: 'hourglass.allows_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allows_chain

/-- info: 'hourglass.one_is_at_most_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_is_at_most_one

/-- info: 'hourglass.span_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms span_law

/-- info: 'hourglass.merge_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms merge_spec

/-- info: 'hourglass.check_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_spec

/-- info: 'hourglass.merge_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms merge_comm

/-- info: 'hourglass.merge_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms merge_self

/-- info: 'hourglass.merge_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms merge_empty

/-- info: 'hourglass.merge_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms merge_assoc

/-- info: 'hourglass.mergeRec_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mergeRec_fits


/-! The rung 3 laws. The laws about `propose` hold for every answer of
    the world queries of the gate, so their pins name those queries. -/

/-- info: 'hourglass.replay_one_of_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms replay_one_of_commit

/-- info: 'hourglass.replay_is_the_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms replay_is_the_world

/-- info: 'hourglass.rewind_is_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rewind_is_exact

/-- info: 'hourglass.propose_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 validate.queries.blank,
 validate.queries.count_faults,
 validate.queries.cycle_through,
 validate.queries.ended_before,
 validate.queries.is_located_in,
 validate.queries.type_faults] -/
#guard_msgs in
#print axioms propose_ok

/-- info: 'hourglass.propose_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 validate.queries.blank,
 validate.queries.count_faults,
 validate.queries.cycle_through,
 validate.queries.ended_before,
 validate.queries.is_located_in,
 validate.queries.type_faults] -/
#guard_msgs in
#print axioms propose_err

/-- info: 'hourglass.reach_propose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 validate.queries.blank,
 validate.queries.count_faults,
 validate.queries.cycle_through,
 validate.queries.ended_before,
 validate.queries.is_located_in,
 validate.queries.type_faults] -/
#guard_msgs in
#print axioms reach_propose

/-! The rung 4a laws: the rules inside `apply`. -/

/-- info: 'hourglass.apply_one_fact_per_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms apply_one_fact_per_slot

/-- info: 'hourglass.apply_keeps_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms apply_keeps_ids

/-- info: 'hourglass.apply_one_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms apply_one_target

/-- info: 'hourglass.every_world_one_fact_per_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms every_world_one_fact_per_slot

/-- info: 'hourglass.entities_never_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entities_never_vanish

/-- info: 'hourglass.every_world_one_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms every_world_one_target

/-! The rung 4b laws: the rules inside `validate`. Each pin names the world
    queries that the law reads, and no other axiom. -/

/-- info: 'hourglass.start_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 validate.queries.count_faults,
 validate.queries.cycle_through,
 validate.queries.ended_before,
 validate.queries.is_located_in,
 validate.queries.type_faults] -/
#guard_msgs in
#print axioms start_clean

/-- info: 'hourglass.update_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms update_clean

/-- info: 'hourglass.validate_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 validate.queries.blank,
 validate.queries.count_faults,
 validate.queries.cycle_through,
 validate.queries.ended_before,
 validate.queries.is_located_in,
 validate.queries.type_faults] -/
#guard_msgs in
#print axioms validate_clean

/-- info: 'hourglass.apply_in_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms apply_in_band

/-- info: 'hourglass.reachP_reach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 validate.queries.blank,
 validate.queries.count_faults,
 validate.queries.cycle_through,
 validate.queries.ended_before,
 validate.queries.is_located_in,
 validate.queries.type_faults] -/
#guard_msgs in
#print axioms reachP_reach

/-- info: 'hourglass.every_proposed_world_in_band' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 validate.queries.blank,
 validate.queries.count_faults,
 validate.queries.cycle_through,
 validate.queries.ended_before,
 validate.queries.is_located_in,
 validate.queries.type_faults] -/
#guard_msgs in
#print axioms every_proposed_world_in_band

/-! The rung 5 direction law. -/

/-- info: 'hourglass.start_dir' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 validate.queries.count_faults,
 validate.queries.cycle_through,
 validate.queries.ended_before,
 validate.queries.is_located_in,
 validate.queries.type_faults] -/
#guard_msgs in
#print axioms start_dir

/-- info: 'hourglass.update_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms update_dir

/-- info: 'hourglass.end_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms end_dir

/-- info: 'hourglass.validate_dir' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 validate.queries.blank,
 validate.queries.count_faults,
 validate.queries.cycle_through,
 validate.queries.ended_before,
 validate.queries.is_located_in,
 validate.queries.type_faults] -/
#guard_msgs in
#print axioms validate_dir

/-- info: 'hourglass.apply_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms apply_up

/-- info: 'hourglass.up_never_falls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 validate.queries.blank,
 validate.queries.count_faults,
 validate.queries.cycle_through,
 validate.queries.ended_before,
 validate.queries.is_located_in,
 validate.queries.type_faults] -/
#guard_msgs in
#print axioms up_never_falls

