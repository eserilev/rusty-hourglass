-- The rung 1 laws: the ten Kani harnesses of src/proofs.rs, as Lean
-- theorems about the code that Aeneas extracted from the crate.
--
-- Kani checks the Rust code with a bounded model checker. Here, each
-- law holds for every input, with no bound, and each theorem also
-- proves that the function never panics: it answers `ok`.
import Hourglass.Funs

open Aeneas Aeneas.Std Result

namespace hourglass

open memory fact time

/-! ## The join of two numbers -/

@[simp] theorem join_larger (x y : Std.I64) :
    Join.of .Larger (.Number x) (.Number y)
      = ok (.Number (core.cmp.impls.OrdI64.max x y)) := by
  simp [Join.of, lift]

@[simp] theorem join_smaller (x y : Std.I64) :
    Join.of .Smaller (.Number x) (.Number y)
      = ok (.Number (core.cmp.impls.OrdI64.min x y)) := by
  simp [Join.of, lift]

private theorem i64_eq {a b : Std.I64} (h : a.val = b.val) : a = b := by
  scalar_tac

/-- Kani: `the_join_answers_the_same_either_way`. -/
theorem join_comm (x y : Std.I64) :
    Join.of .Larger (.Number x) (.Number y) = Join.of .Larger (.Number y) (.Number x) ∧
    Join.of .Smaller (.Number x) (.Number y) = Join.of .Smaller (.Number y) (.Number x) := by
  simp only [join_larger, join_smaller, ok.injEq, Value.Number.injEq]
  constructor <;> apply i64_eq <;> simp <;> omega

/-- Kani: `the_join_ignores_the_grouping`. -/
theorem join_assoc (x y z : Std.I64) :
    (do let ab ← Join.of .Larger (.Number x) (.Number y); Join.of .Larger ab (.Number z))
      = (do let bc ← Join.of .Larger (.Number y) (.Number z); Join.of .Larger (.Number x) bc) ∧
    (do let ab ← Join.of .Smaller (.Number x) (.Number y); Join.of .Smaller ab (.Number z))
      = (do let bc ← Join.of .Smaller (.Number y) (.Number z); Join.of .Smaller (.Number x) bc) := by
  simp only [join_larger, join_smaller, bind_tc_ok, ok.injEq, Value.Number.injEq]
  constructor <;> apply i64_eq <;> simp

/-- Kani: `the_join_of_one_record_with_itself_is_that_record`. -/
theorem join_idem (x : Std.I64) :
    Join.of .Larger (.Number x) (.Number x) = ok (.Number x) ∧
    Join.of .Smaller (.Number x) (.Number x) = ok (.Number x) := by
  simp only [join_larger, join_smaller, ok.injEq, Value.Number.injEq]
  constructor <;> apply i64_eq <;> simp

/-- Kani: `the_join_never_moves_backward`. -/
theorem join_never_backward (x y : Std.I64) :
    (∃ n, Join.of .Larger (.Number x) (.Number y) = ok (.Number n)
          ∧ x.val ≤ n.val ∧ y.val ≤ n.val) ∧
    (∃ n, Join.of .Smaller (.Number x) (.Number y) = ok (.Number n)
          ∧ n.val ≤ x.val ∧ n.val ≤ y.val) := by
  simp only [join_larger, join_smaller, ok.injEq, Value.Number.injEq, exists_eq_left']
  simp

/-- A new law, past Kani: the join never panics, for every join and
    every pair of values, of any shape. -/
theorem join_total (j : Join) (a b : Value) : ∃ v, Join.of j a b = ok v := by
  cases j <;> cases a <;> cases b <;> simp [Join.of, lift]

/-! ## The band -/

/-- Kani: `the_join_of_two_numbers_in_a_band_stays_in_the_band`. -/
theorem join_stays_in_band (band : Band) (x y : Std.I64)
    (hx : band.holds x = ok true) (hy : band.holds y = ok true) :
    (∃ n, Join.of .Larger (.Number x) (.Number y) = ok (.Number n) ∧ band.holds n = ok true) ∧
    (∃ n, Join.of .Smaller (.Number x) (.Number y) = ok (.Number n) ∧ band.holds n = ok true) := by
  simp only [Band.holds] at hx hy ⊢
  simp only [join_larger, join_smaller, ok.injEq, Value.Number.injEq, exists_eq_left']
  split at hx <;> split at hy <;> simp_all

/-- Kani: `a_number_lands_inside_its_band`. -/
theorem clamp_lands (band : Band) (n : Std.I64) (h : band.min.val ≤ band.max.val) :
    ∃ g, band.clamp n = ok g ∧ band.holds g = ok true ∧ band.clamp g = ok g ∧
      (band.holds n = ok true → g = n) := by
  simp only [Band.clamp, Band.holds]
  split <;> [skip; split] <;> simp_all <;> split <;> simp_all <;> omega

/-- Kani: `a_wider_band_holds_every_old_number`. -/
theorem wider_band_holds (was now : Band) (n : Std.I64)
    (hin : was.inside now = ok true) (hn : was.holds n = ok true) :
    now.holds n = ok true := by
  simp only [Band.inside, Band.holds] at *
  split at hin <;> split at hn <;> simp_all
  split <;> simp_all <;> omega

/-! ## The direction -/

/-- Kani: `a_write_the_direction_allows_keeps_the_order`. -/
theorem allows_chain (a b c : Std.I64) :
    (Direction.Up.allows a b = ok true → Direction.Up.allows b c = ok true → a.val ≤ c.val) ∧
    (Direction.Down.allows a b = ok true → Direction.Down.allows b c = ok true → c.val ≤ a.val) := by
  simp only [Direction.allows, ok.injEq, decide_eq_true_eq]
  constructor <;> intro h1 h2 <;> scalar_tac

/-! ## The count -/

/-- Kani: `one_is_at_most_one`. -/
theorem one_is_at_most_one (n : Std.U16) (hn : 1 < n.val) :
    Count.One.limit = (Count.AtMost 1#u16).limit ∧
    Count.One.is_single = ok true ∧
    (Count.AtMost 1#u16).is_single = ok true ∧
    (Count.AtMost n).is_single = ok false ∧
    Count.Many.is_single = ok false := by
  simp only [Count.is_single, Count.limit, bind_tc_ok,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq]
  simp
  scalar_tac

/-! ## The span -/

/-- Kani: `a_span_holds_its_start_and_not_its_end`. -/
theorem span_law («from» «until» «at» : time.Tick) (h : «from».val ≤ «until».val) :
    (TimeSpan.closed «from» «until» >>= TimeSpan.sound) = ok true ∧
    (TimeSpan.closed «from» «until» >>= fun s => s.holds_at «until») = ok false ∧
    (TimeSpan.closed «from» «until» >>= fun s => s.holds_at «at»)
      = ok (decide («from».val ≤ «at».val ∧ «at».val < «until».val)) ∧
    (TimeSpan.open «from» >>= fun s => s.holds_at «at») = ok (decide («from».val ≤ «at».val)) := by
  simp only [TimeSpan.closed, TimeSpan.open, TimeSpan.sound, TimeSpan.holds_at, bind_tc_ok,
    time.Tick.Insts.CoreCmpPartialOrdTick.lt, time.Tick.Insts.CoreCmpPartialOrdTick.ge]
  -- The order on `Tick` is the order on its u64 value.
  have lt (a b : time.Tick) : (a < b) = (a.val < b.val) := rfl
  have ge (a b : time.Tick) : (a ≥ b) = (b.val ≤ a.val) := rfl
  simp only [lt, ge]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try split) <;> simp_all

end hourglass
