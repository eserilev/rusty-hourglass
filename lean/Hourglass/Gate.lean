-- The rung 4b laws: the rules inside `validate`.
--
-- `validate` translates in full, except its world queries
-- (FunsExternal.lean). The queries only answer values, so the laws hold
-- for every answer they give.
import Hourglass.Apply
import Hourglass.Merge

open Aeneas Aeneas.Std Result

namespace hourglass

open world event fact entity

/-! ## The list of faults only grows -/

/-- Every `ok` answer of `m` extends the list `o`. It is irreducible, so
    `intro` in the `grows` tactic never opens it by accident. -/
@[irreducible] def Grows (o : alloc.vec.Vec reject.Rejection) (m : Result (alloc.vec.Vec reject.Rejection)) :
    Prop :=
  ∀ r, m = ok r → o.val <+: r.val

theorem grows_ok {o x : alloc.vec.Vec reject.Rejection} (h : o.val <+: x.val) :
    Grows o (ok x) := by
  unfold Grows; intro r hr; simp only [ok.injEq] at hr; subst hr; exact h

theorem grows_push {o x : alloc.vec.Vec reject.Rejection} {y : reject.Rejection}
    (h : o.val <+: x.val) : Grows o (alloc.vec.Vec.push x y) := by
  unfold Grows; intro r hr
  rw [push_val_any hr]
  exact h.trans (List.prefix_append _ _)

theorem push_all_loop_prefix (s : Slice reject.Rejection) :
    ∀ (n : Nat) (x r : alloc.vec.Vec reject.Rejection) (i : Usize), s.length - i.val = n →
      validate.push_all_loop x s i = ok r → x.val <+: r.val := by
  intro n
  induction n with
  | zero =>
    intro x r i hn h
    rw [validate.push_all_loop] at h
    have hge : ¬ i < Slice.len s := by scalar_tac
    simp only [hge, if_false, ok.injEq] at h
    subst h; exact List.prefix_refl _
  | succ n ih =>
    intro x r i hn h
    rw [validate.push_all_loop] at h
    have hc : i < Slice.len s := by scalar_tac
    simp only [hc, if_true] at h
    rw [bind_eq_ok] at h; obtain ⟨_, _, h⟩ := h
    rw [bind_eq_ok] at h; obtain ⟨_, _, h⟩ := h
    rw [bind_eq_ok] at h; obtain ⟨x1, hx1, h⟩ := h
    rw [bind_eq_ok] at h; obtain ⟨i2, hi2, h⟩ := h
    have hv := push_val_any hx1
    obtain ⟨_, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [hadd] at hi2; simp only [ok.injEq] at hi2; subst hi2
    have := ih x1 r _ (by scalar_tac) h
    rw [hv] at this
    exact (List.prefix_append _ _).trans this

theorem grows_push_all {o x : alloc.vec.Vec reject.Rejection} {s : Slice reject.Rejection}
    (h : o.val <+: x.val) : Grows o (validate.push_all x s) := by
  unfold Grows; intro r hr
  exact h.trans (push_all_loop_prefix s _ x r 0#usize rfl hr)

theorem grows_target_fits {o x : alloc.vec.Vec reject.Rejection} {n : String}
    {rules : FactRules} {l : Option time.EntityId} (h : o.val <+: x.val) :
    Grows o (validate.target_fits n rules l x) := by
  unfold Grows; intro r hr
  unfold validate.target_fits at hr
  simp only [alloc.string.String.Insts.CoreCloneClone.clone, bind_tc_ok] at hr
  rcases rules with _ | _ <;> cases l <;>
    simp [FactRules.takes_target] at hr <;>
    first
    | (subst hr; exact h)
    | (rw [push_val_any hr]; exact h.trans (List.prefix_append _ _))

theorem grows_bind_vec {o : alloc.vec.Vec reject.Rejection}
    {m : Result (alloc.vec.Vec reject.Rejection)}
    {f : alloc.vec.Vec reject.Rejection → Result (alloc.vec.Vec reject.Rejection)}
    (hm : Grows o m) (hf : ∀ a, o.val <+: a.val → Grows o (f a)) : Grows o (m >>= f) := by
  unfold Grows at *; intro r hr
  rw [bind_eq_ok] at hr
  obtain ⟨a, ha, hr⟩ := hr
  exact hf a (hm a ha) r hr

theorem grows_bind {β : Type} {o : alloc.vec.Vec reject.Rejection} {m : Result β}
    {f : β → Result (alloc.vec.Vec reject.Rejection)}
    (hf : ∀ a, Grows o (f a)) : Grows o (m >>= f) := by
  unfold Grows at *; intro r hr
  rw [bind_eq_ok] at hr
  obtain ⟨a, _, hr⟩ := hr
  exact hf a r hr

/-- Close a `Grows` goal through binds, branches, and pushes. It fails
    when it gets stuck, so a bind on a fresh list (for example the
    faults of a query) falls back to the plain bind rule. -/
syntax "grows" : tactic
macro_rules
  | `(tactic| grows) => `(tactic| first
    | (apply grows_ok; assumption)
    | (apply grows_push; assumption)
    | (apply grows_push_all; assumption)
    | (apply grows_target_fits; assumption)
    | (refine grows_bind_vec (by grows) (fun _ _ => by grows))
    | (refine grows_bind (fun _ => by grows))
    | (split <;> grows))

theorem grows_of {o r : alloc.vec.Vec reject.Rejection} {m : Result (alloc.vec.Vec reject.Rejection)}
    (hg : Grows o m) (h : m = ok r) : o.val <+: r.val := by
  unfold Grows at hg; exact hg r h

theorem nil_of_prefix_nil {a b : List reject.Rejection} (h : a <+: b) (hb : b = []) : a = [] := by
  subst hb; exact List.prefix_nil.1 h

theorem push_ne {o r : alloc.vec.Vec reject.Rejection} {x : reject.Rejection}
    (h : alloc.vec.Vec.push o x = ok r) : r.val ≠ [] := by
  rw [push_val_any h]; simp

/-! ## A clean start, and a clean update -/

/-- A value fits its shape: a flag holds no number, and a number sits
    in its band. -/
def numOk : Shape → Option Std.I64 → Prop
  | .Flag _, v => v = none
  | .Number band _, v => ∃ n, v = some n ∧ bandHolds band n = true

theorem number_fits_grows (nm : String) (sh : Shape) (v : Option Std.I64)
    (o : alloc.vec.Vec reject.Rejection) : Grows o (validate.number_fits nm sh v o) := by
  have ho : o.val <+: o.val := List.prefix_refl _
  unfold validate.number_fits
  grows

theorem number_fits_clean {nm : String} {sh : Shape} {v : Option Std.I64}
    {o o' : alloc.vec.Vec reject.Rejection} (h : validate.number_fits nm sh v o = ok o')
    (he : o'.val = []) : numOk sh v := by
  unfold validate.number_fits at h
  simp only [alloc.string.String.Insts.CoreCloneClone.clone, bind_tc_ok, holds_eq] at h
  cases sh <;> cases v <;> simp only at h
  · rfl
  · exact absurd he (push_ne h)
  · exact absurd he (push_ne h)
  · rename_i band _ n
    split at h
    · exact ⟨n, rfl, by assumption⟩
    · exact absurd he (push_ne h)

/-- A START WITH NO FAULT names a declared fact, with a value that
    fits the shape of the name. -/
theorem start_clean {w : World} {who : time.EntityId} {nm : String} {v : Option Std.I64}
    {lt : Option time.EntityId} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.start w who nm v lt o = ok o') (he : o'.val = []) :
    ∃ r, (w.vocabulary.names : names.Names FactRules)[nm]? = some r ∧ numOk (shapeOf r) v := by
  unfold validate.start at h
  rw [bind_eq_ok] at h
  obtain ⟨⟨holder, out1⟩, _, h⟩ := h
  simp only [FactVocabulary.rules_key, names.Names.get_key] at h
  simp at h
  cases hr : (w.vocabulary.names : names.Names FactRules)[nm]? with
  | none =>
    simp [hr, alloc.string.String.Insts.CoreCloneClone.clone] at h
    exact absurd he (push_ne h)
  | some r =>
    simp [hr] at h
    rw [bind_eq_ok] at h
    obtain ⟨out2, h2, h⟩ := h
    have hrefl : out2.val <+: out2.val := List.prefix_refl _
    have hp : out2.val <+: o'.val := grows_of (by grows) h
    have h2e : out2.val = [] := nil_of_prefix_nil hp he
    exact ⟨r, rfl, number_fits_clean h2 h2e⟩

/-- AN UPDATE WITH NO FAULT names a declared number fact, and the new
    value sits in its band. -/
theorem update_clean {w : World} {who : time.EntityId} {nm : String}
    {lt : Option time.EntityId} {fr tv : Std.I64} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.update w who nm lt fr tv o = ok o') (he : o'.val = []) :
    ∃ r band d, (w.vocabulary.names : names.Names FactRules)[nm]? = some r ∧
      shapeOf r = .Number band d ∧ bandHolds band tv = true := by
  unfold validate.update at h
  rw [bind_eq_ok] at h
  obtain ⟨⟨holder, out1⟩, _, h⟩ := h
  simp only [FactVocabulary.rules_key, names.Names.get_key] at h
  simp at h
  cases hr : (w.vocabulary.names : names.Names FactRules)[nm]? with
  | none =>
    simp [hr, alloc.string.String.Insts.CoreCloneClone.clone] at h
    exact absurd he (push_ne h)
  | some r =>
    simp [hr] at h
    rw [bind_eq_ok] at h
    obtain ⟨out2, h2, h⟩ := h
    have hrefl : out2.val <+: out2.val := List.prefix_refl _
    have hp : out2.val <+: o'.val := grows_of (by grows) h
    have h2e : out2.val = [] := nil_of_prefix_nil hp he
    cases hs : shapeOf r with
    | Flag d =>
      simp [hs, alloc.string.String.Insts.CoreCloneClone.clone] at h2
      exact absurd h2e (push_ne h2)
    | Number band d =>
      simp only [hs, alloc.string.String.Insts.CoreCloneClone.clone, bind_tc_ok] at h2
      rw [bind_eq_ok] at h2
      obtain ⟨out3, h3, h2⟩ := h2
      have hrefl3 : out3.val <+: out3.val := List.prefix_refl _
      have hp3 : out3.val <+: out2.val := grows_of (by grows) h2
      have h3e : out3.val = [] := nil_of_prefix_nil hp3 h2e
      refine ⟨r, band, d, rfl, hs, ?_⟩
      split at h3
      · assumption
      · exact absurd h3e (push_ne h3)

/-! ## What a clean gate says about an event -/

/-- What a clean gate says about the kind of an event: a start names a
    declared fact with a value that fits its shape, and an update names
    a declared number fact with a new value in its band. -/
def cleanKind (v : FactVocabulary) : EventKind → Prop
  | .FactStart _ nm value _ =>
    ∃ r, (v.names : names.Names FactRules)[nm]? = some r ∧ numOk (shapeOf r) value
  | .FactUpdate _ nm _ _ tv =>
    ∃ r band d, (v.names : names.Names FactRules)[nm]? = some r ∧
      shapeOf r = .Number band d ∧ bandHolds band tv = true
  | _ => True

/-- A GATE WITH NO FAULT passes only a clean event. -/
theorem validate_clean {w : World} {t : time.Tick} {k : EventKind}
    {f : alloc.vec.Vec reject.Rejection}
    (h : validate.validate w t k = ok f) (he : f.val = []) : cleanKind w.vocabulary k := by
  unfold validate.validate at h
  rw [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out, _, h⟩ := h
  cases k with
  | FactStart who nm value lt => exact start_clean h he
  | FactUpdate who nm lt fr tv => exact update_clean h he
  | _ => trivial

/-! ## Every number sits in its band -/

/-- Every fact carries a declared name, and its value fits the shape of
    that name: a flag holds no number, and a number sits in its band. -/
def inBand (v : FactVocabulary) (m : ids.Ids Entity) : Prop :=
  ∀ (k : Nat) (e : Entity) (x : Fact), (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e →
    x ∈ e.facts.val →
    ∃ r, (v.names : names.Names FactRules)[x.name]? = some r ∧ numOk (shapeOf r) x.value

theorem ib_erase {v : FactVocabulary} {m : ids.Ids Entity} (h : inBand v m) (k : Nat) :
    inBand v (Std.ExtTreeMap.erase m k) := by
  intro j e x hj hx
  rw [Std.ExtTreeMap.getElem?_erase] at hj
  split at hj
  · simp at hj
  · exact h j e x hj hx

theorem ib_insert {v : FactVocabulary} {m : ids.Ids Entity} (h : inBand v m) (k : Nat)
    (row : Entity) (hr : ∀ x ∈ row.facts.val,
      ∃ r, (v.names : names.Names FactRules)[x.name]? = some r ∧ numOk (shapeOf r) x.value) :
    inBand v (Std.ExtTreeMap.insert m k row) := by
  intro j e x hj hx
  rw [Std.ExtTreeMap.getElem?_insert] at hj
  split at hj
  · simp only [Option.some.injEq] at hj; subst hj; exact hr x hx
  · exact h j e x hj hx

/-- APPLY KEEPS EVERY NUMBER IN ITS BAND, for a clean event. -/
theorem apply_in_band (m : ids.Ids Entity) (v : FactVocabulary) (ev : Event)
    (m' : ids.Ids Entity) (h : inBand v m) (hc : cleanKind v ev.kind)
    (ha : World.apply m v ev = ok m') : inBand v m' := by
  unfold World.apply at ha
  cases hk : ev.kind <;> simp only [hk] at ha <;> rw [hk] at hc
  case EntityCreated id ty nm =>
    simp only [ids.Ids.contains, bind_tc_ok] at ha
    split at ha
    · simp only [ok.injEq] at ha; subst ha; exact h
    · simp only [alloc.string.String.Insts.CoreCloneClone.clone, time.TimeSpan.open,
        ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
      subst ha
      exact ib_insert h _ _ (fun x hx => by simp [alloc.vec.Vec.new] at hx)
  case EntityDestroyed id =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[id.val]? with
    | none => simp [hr] at ha; subst ha; exact ib_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      split at ha
      all_goals
        simp only [bind_tc_ok, ok.injEq] at ha
        subst ha
        exact ib_insert (ib_erase h _) _ _ (fun x hx => h _ _ x hr hx)
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨wide, _, ha⟩ := ha
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact ib_erase h _
    | some row =>
      simp [hr, ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨v1, hv1, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply ib_insert (ib_erase h _)
      intro x hx
      rw [push_val_any hv1, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · -- An old fact that the drop kept.
        have hsub : x ∈ row.facts.val := by
          cases wide
          · simp only [Bool.false_eq_true, if_false, world.drop_slot] at hvf
            rw [drop_slot_ok hvf, List.mem_filter] at hx; exact hx.1
          · simp only [if_true, world.drop_name] at hvf
            rw [drop_name_ok hvf, List.mem_filter] at hx; exact hx.1
        exact h _ _ x hr hsub
      · -- The new fact: the gate checked its name and its value.
        exact hc
  case FactUpdate who nm lt fr tv =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact ib_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨o1, ho1, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply ib_insert (ib_erase h _)
      cases o1 with
      | none =>
        simp only [ok.injEq] at hvf; subst hvf
        exact fun x hx => h _ _ x hr hx
      | some i =>
        obtain ⟨_, ho1', hlt⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
          (slot_index_spec row.facts.deref nm lt)
        rw [ho1] at ho1'
        simp only [ok.injEq] at ho1'
        subst ho1'
        have hj := (hlt i rfl).fst
        have hin := (hlt i rfl).snd
        have hi : i.val < row.facts.val.length := by simpa [alloc.vec.Vec.deref] using hj
        have hname : (row.facts.val[i.val]).name = nm := by
          simp [inSlot, slotOf, alloc.vec.Vec.deref] at hin
          exact hin.1
        simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize] at hvf
        simp [hi] at hvf
        subst hvf
        intro x hx
        simp only [alloc.vec.Vec.set_val_eq, List.set_set] at hx
        rcases List.mem_or_eq_of_mem_set hx with hx | hx
        · exact h _ _ x hr hx
        · rw [hx]
          -- The updated fact: its name is the name of the event, and
          -- the gate checked the new value against the band.
          obtain ⟨r, band, d, hr', hs, hb⟩ := hc
          refine ⟨r, ?_, ?_⟩
          · simpa [hname] using hr'
          · simp only [hs, numOk]
            exact ⟨tv, rfl, hb⟩
  case FactEnd who nm lt =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact ib_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply ib_insert (ib_erase h _)
      intro x hx
      rw [drop_slot_ok hvf, List.mem_filter] at hx
      exact h _ _ x hr hx.1

/-! ## Every world that proposals build -/

/-- `ReachP w u`: proposals, landed or refused, turn `w` into `u`. -/
inductive ReachP : World → World → Prop
  | refl (w : World) : ReachP w w
  | step {w u u' : World} {t : time.Tick} {k : EventKind}
      {r : core.result.Result time.EventId (alloc.vec.Vec reject.Rejection)} :
      ReachP w u → World.propose u t k = ok (r, u') → ReachP w u'

/-- A world that proposals build is also a world that commits build, so
    every law of the rungs before holds for it too. -/
theorem reachP_reach {w u : World} (h : ReachP w u) : Reach w u := by
  induction h with
  | refl => exact Reach.refl _
  | step _ hp ih => exact reach_propose ih hp

theorem reachP_in_band {w u : World} (hr : ReachP w u)
    (h : inBand w.vocabulary w.entities) : inBand u.vocabulary u.entities := by
  induction hr with
  | refl => exact h
  | @step u u' t k r _ hp ih =>
    cases r with
    | Err f => rw [(propose_err u u' t k f hp).1]; exact ih
    | Ok id =>
      obtain ⟨⟨f, hv, he⟩, hc⟩ := propose_ok u u' t k id hp
      obtain ⟨_, _, hvoc⟩ := commit_ok hc
      rw [hvoc]
      exact apply_in_band _ _ _ _ ih (validate_clean hv he) (commit_apply hc)

/-- EVERY NUMBER SITS IN ITS BAND, IN EVERY WORLD THAT PROPOSALS BUILD.
    Every fact carries a declared name, a flag holds no number, and a
    number sits inside the band of its name. -/
theorem every_proposed_world_in_band (v : FactVocabulary) (w0 w : World)
    (h0 : World.new v = ok w0) (hr : ReachP w0 w) : inBand w.vocabulary w.entities := by
  apply reachP_in_band hr
  simp only [World.new, ids.Ids.new, EventHistory.new, bind_tc_ok, ok.injEq] at h0
  subst h0
  intro k e x hk
  simp at hk

end hourglass
