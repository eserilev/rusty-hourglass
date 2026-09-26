-- The trust check. Each law depends only on the three standard axioms
-- of Lean. A `sorry` or a new axiom changes the output, and the build fails.
import Hourglass.Laws
import Hourglass.Merge

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

