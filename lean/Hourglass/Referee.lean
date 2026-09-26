-- The rung 9 law: the referee passes every world that proposals build.
import Hourglass.Cycle

open Aeneas Aeneas.Std Result

namespace hourglass

open world event fact entity

/-! ## The list of faults only grows, through every branch -/

theorem grows_number_fits {o x : alloc.vec.Vec reject.Rejection} {nm : String} {sh : Shape}
    {v : Option Std.I64} (h : o.val <+: x.val) : Grows o (validate.number_fits nm sh v x) := by
  unfold Grows; intro r hr
  exact h.trans (grows_of (number_fits_grows nm sh v x) hr)

/-- `grows`, through a `have` inside the body. -/
macro_rules
  | `(tactic| grows) => `(tactic| (dsimp only; grows))

/-- `grows`, and the number check of the gate. -/
macro_rules
  | `(tactic| grows) => `(tactic| (apply grows_number_fits; assumption))

theorem live_holder_grows {w : World} {who : time.EntityId} {o o' : alloc.vec.Vec reject.Rejection}
    {b : Bool} (h : validate.live_holder w who o = ok (b, o')) : o.val <+: o'.val := by
  unfold validate.live_holder at h
  simp only [entity_eq, bind_tc_ok] at h
  split at h
  · rw [bind_eq_ok] at h
    obtain ⟨o1, h1, h⟩ := h
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    rw [push_val_any h1]; exact List.prefix_append _ _
  · rw [bind_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    split at h
    · rw [bind_eq_ok] at h
      obtain ⟨o1, h1, h⟩ := h
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      rw [push_val_any h1]; exact List.prefix_append _ _
    · simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact List.prefix_refl _

theorem grows_start {o x : alloc.vec.Vec reject.Rejection} {w : World} {who : time.EntityId}
    {nm : String} {v : Option Std.I64} {lt : Option time.EntityId} (h : o.val <+: x.val) :
    Grows o (validate.start w who nm v lt x) := by
  unfold Grows; intro r hr
  unfold validate.start at hr
  rw [bind_eq_ok] at hr
  obtain ⟨⟨_, x1⟩, h1, hr⟩ := hr
  have p1 := h.trans (live_holder_grows h1)
  have hx : x1.val <+: x1.val := List.prefix_refl _
  exact p1.trans (grows_of (by grows) hr)

theorem grows_update {o x : alloc.vec.Vec reject.Rejection} {w : World} {who : time.EntityId}
    {nm : String} {lt : Option time.EntityId} {fr tv : Std.I64} (h : o.val <+: x.val) :
    Grows o (validate.update w who nm lt fr tv x) := by
  unfold Grows; intro r hr
  unfold validate.update at hr
  rw [bind_eq_ok] at hr
  obtain ⟨⟨_, x1⟩, h1, hr⟩ := hr
  have p1 := h.trans (live_holder_grows h1)
  have hx : x1.val <+: x1.val := List.prefix_refl _
  exact p1.trans (grows_of (by grows) hr)

theorem grows_end {o x : alloc.vec.Vec reject.Rejection} {w : World} {who : time.EntityId}
    {nm : String} {lt : Option time.EntityId} (h : o.val <+: x.val) :
    Grows o (validate.end w who nm lt x) := by
  unfold validate.end
  grows

/-! ## What a clean gate says, for the referee -/

/-- The top of the gate: a clean event does not go back in time, and
    the check of its kind starts from an empty list. -/
theorem validate_top {w : World} {t : time.Tick} {k : EventKind}
    {f : alloc.vec.Vec reject.Rejection}
    (h : validate.validate w t k = ok f) (he : f.val = []) :
    w.tick.val ≤ t.val := by
  unfold validate.validate at h
  simp only [time.Tick.Insts.CoreCmpPartialOrdTick.lt, bind_tc_ok] at h
  by_cases hlt : t < w.tick
  · exfalso
    simp only [hlt, decide_true, if_true] at h
    rw [bind_eq_ok] at h
    obtain ⟨out, hout, h⟩ := h
    have hr : out.val <+: out.val := List.prefix_refl _
    have p : out.val <+: f.val := by
      refine grows_of ?_ h
      split
      · grows
      · grows
      · exact grows_start hr
      · exact grows_update hr
      · exact grows_end hr
    have := nil_of_prefix_nil p he
    exact push_ne hout this
  · have : ¬ t.val < w.tick.val := fun h' => hlt h'
    omega

/-- A clean creation names a new id. -/
theorem validate_created {w : World} {t : time.Tick} {id : time.EntityId} {ty : EntityType}
    {nm : String} {f : alloc.vec.Vec reject.Rejection}
    (h : validate.validate w t (.EntityCreated id ty nm) = ok f) (he : f.val = []) :
    (w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]? = none := by
  unfold validate.validate at h
  rw [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out, _, h⟩ := h
  simp only at h
  rw [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out1, _, h⟩ := h
  simp only [entity_eq, bind_tc_ok] at h
  cases hm : (w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]? with
  | none => rfl
  | some _ =>
    simp [hm] at h
    exact absurd he (push_ne h)


theorem type_of_eq (w : World) (id : time.EntityId) :
    World.type_of w id =
      ok (((w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]?).map (fun e => e.entity_type)) := by
  unfold World.type_of
  simp only [ids.Ids.get, bind_tc_ok]
  cases (w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]? <;> rfl

/-- A clean type check: when both ends exist, the type map allows the pair. -/
theorem types_fit_clean {w : World} {who : time.EntityId} {nm : String} {r : FactRules}
    {t : time.EntityId} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.types_fit w who nm r t o = ok o') (he : o'.val = []) :
    ∀ a b, (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? = some a →
      (w.entities : Std.ExtTreeMap Nat Entity compare)[t.val]? = some b →
      FactRules.type_allowed r a.entity_type b.entity_type = ok true := by
  intro a b ha hb
  unfold validate.types_fit at h
  simp only [type_of_eq, ha, hb, Option.map_some, bind_tc_ok] at h
  cases hr : FactRules.type_allowed r a.entity_type b.entity_type <;> rw [hr] at h
  case ret c =>
    simp only [bind_tc_ok] at h
    cases c
    · simp only [Bool.false_eq_true, if_false] at h
      rw [bind_eq_ok] at h
      obtain ⟨_, _, h⟩ := h
      exact absurd he (push_ne h)
    · rfl
  all_goals simp at h

/-- A CLEAN START OF A LINK. The target is not the holder, the target
    exists, and the type map allows the pair. -/
theorem start_link_clean {w : World} {who : time.EntityId} {nm : String} {v : Option Std.I64}
    {tgt : time.EntityId} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.start w who nm v (some tgt) o = ok o') (he : o'.val = [])
    {row : Entity} (hrow : (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? = some row) :
    tgt ≠ who ∧ ∃ e2 r, (w.entities : Std.ExtTreeMap Nat Entity compare)[tgt.val]? = some e2 ∧
      (w.vocabulary.names : names.Names FactRules)[nm]? = some r ∧
      (takesT r = true → FactRules.type_allowed r row.entity_type e2.entity_type = ok true) := by
  unfold validate.start at h
  rw [bind_eq_ok] at h
  obtain ⟨⟨holder, out1⟩, h1, h⟩ := h
  simp only [FactVocabulary.rules_key, names.Names.get_key, bind_tc_ok] at h
  cases hr : (w.vocabulary.names : names.Names FactRules)[nm]? with
  | none =>
    simp [hr] at h
    rw [bind_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    exact absurd he (push_ne h)
  | some rules =>
    simp [hr] at h
    rw [bind_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨out5, h5, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨x, hx, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨o4, h4, h⟩ := h
    have hr4 : o4.val <+: o4.val := List.prefix_refl _
    have e4 := nil_of_prefix_nil (grows_of (by grows) h) he
    have hrx : x.val <+: x.val := List.prefix_refl _
    have ex := nil_of_prefix_nil (grows_of (by grows) h4) e4
    have hr5 : out5.val <+: out5.val := List.prefix_refl _
    have e5 := nil_of_prefix_nil (grows_of (by grows) hx) ex
    simp only [time.EntityId.Insts.CoreCmpPartialEqEntityId.eq, ok.injEq] at hb
    subst hb
    by_cases hne : tgt = who
    · simp only [hne, decide_true, if_true] at h5
      exact absurd e5 (push_ne h5)
    · simp only [hne, decide_false, Bool.false_eq_true, if_false, entity_eq, bind_tc_ok] at h5
      cases he2 : (w.entities : Std.ExtTreeMap Nat Entity compare)[tgt.val]? with
      | none =>
        simp [he2] at h5
        exact absurd e5 (push_ne h5)
      | some e2 =>
        refine ⟨hne, e2, rules, rfl, rfl, fun ht => ?_⟩
        simp only [ht, if_true] at hx
        rw [bind_eq_ok] at hx
        obtain ⟨out7, h7, hx⟩ := hx
        have hr7 : out7.val <+: out7.val := List.prefix_refl _
        have e7 := nil_of_prefix_nil (grows_of (by grows) hx) ex
        exact types_fit_clean h7 e7 row e2 hrow he2


/-! ## What `apply` does to one row -/

/-- Where a fact after `apply` comes from: an old fact of the row, or a
    fact that this event opened. -/
def factFrom (m : ids.Ids Entity) (ev : Event) (k : Nat) (x : Fact) : Prop :=
  (∃ e, (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e ∧ x ∈ e.facts.val) ∨
  (x.opened = ev.id ∧ ∃ who, who.val = k ∧
    ((∃ v, ev.kind = .FactStart who x.name v x.linked_to) ∨
     (∃ e y fr tv, (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e ∧ y ∈ e.facts.val ∧
        slotOf y = slotOf x ∧ ev.kind = .FactUpdate who x.name x.linked_to fr tv)))

/-- Where a row after `apply` comes from. -/
def rowFrom (m : ids.Ids Entity) (ev : Event) (k : Nat) (e' : Entity) : Prop :=
  (∃ e, (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e ∧ e'.id = e.id ∧
    e'.entity_type = e.entity_type ∧ e'.name = e.name ∧
    e'.existence.from = e.existence.from ∧
    (e'.existence.until = e.existence.until ∨
      (e.existence.until = none ∧ e'.existence.until = some ev.tick)) ∧
    ∀ x ∈ e'.facts.val, factFrom m ev k x) ∨
  ((m : Std.ExtTreeMap Nat Entity compare)[k]? = none ∧ ∃ id ty nm, id.val = k ∧
    ev.kind = .EntityCreated id ty nm ∧
    e' = { id := id, entity_type := ty, «name» := nm,
           existence := { «from» := ev.tick, «until» := none },
           facts := alloc.vec.Vec.new Fact })

theorem rowFrom_same {m : ids.Ids Entity} {ev : Event} {k : Nat} {e : Entity}
    (h : (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e) : rowFrom m ev k e :=
  Or.inl ⟨e, h, rfl, rfl, rfl, rfl, Or.inl rfl, fun x hx => Or.inl ⟨e, h, hx⟩⟩

/-- Replace the row at `k`: every other key keeps its row. -/
theorem rowFrom_replace {m : ids.Ids Entity} {ev : Event} {k : Nat} {row' : Entity}
    (hk : rowFrom m ev k row') :
    ∀ j e', (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k row' :
      Std.ExtTreeMap Nat Entity compare)[j]? = some e' → rowFrom m ev j e' := by
  intro j e' hj
  rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase] at hj
  by_cases hkj : k = j
  · subst hkj
    simp at hj
    subst hj; exact hk
  · have : ¬ compare k j = .eq := by simpa using hkj
    simp only [this, if_false] at hj
    exact rowFrom_same hj

theorem rowFrom_erase {m : ids.Ids Entity} {ev : Event} (k : Nat) :
    ∀ j e', (Std.ExtTreeMap.erase m k : Std.ExtTreeMap Nat Entity compare)[j]? = some e' →
      rowFrom m ev j e' := by
  intro j e' hj
  rw [Std.ExtTreeMap.getElem?_erase] at hj
  split at hj
  · simp at hj
  · exact rowFrom_same hj

/-- THE SHAPE OF `apply`. Every row after `apply` comes from the old row
    at its key, or it is the new row of a creation. -/
theorem apply_shape (m : ids.Ids Entity) (v : FactVocabulary) (ev : Event) (m' : ids.Ids Entity)
    (ha : World.apply m v ev = ok m') :
    ∀ k e', (m' : Std.ExtTreeMap Nat Entity compare)[k]? = some e' → rowFrom m ev k e' := by
  unfold World.apply at ha
  cases hkd : ev.kind <;> simp only [hkd] at ha
  case EntityCreated id ty nm =>
    simp only [ids.Ids.contains, bind_tc_ok] at ha
    split at ha
    · simp only [ok.injEq] at ha; subst ha; exact fun k e' h => rowFrom_same h
    · rename_i hnot
      simp only [alloc.string.String.Insts.CoreCloneClone.clone, time.TimeSpan.open,
        ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
      subst ha
      intro j e' hj
      rw [Std.ExtTreeMap.getElem?_insert] at hj
      split at hj
      · rename_i hij
        have hk : id.val = j := by simpa using hij
        simp only [Option.some.injEq] at hj
        subst hj
        refine Or.inr ⟨?_, id, ty, nm, hk, hkd, rfl⟩
        rw [← hk]; simpa using hnot
      · exact rowFrom_same hj
  case EntityDestroyed id =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[id.val]? with
    | none => simp [hr] at ha; subst ha; exact rowFrom_erase _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      split at ha
      · rename_i hu
        simp only [bind_tc_ok, ok.injEq] at ha
        subst ha
        apply rowFrom_replace
        refine Or.inl ⟨row, hr, rfl, rfl, rfl, rfl, Or.inr ⟨?_, rfl⟩,
          fun x hx => Or.inl ⟨row, hr, hx⟩⟩
        simpa using hu
      · simp only [bind_tc_ok, ok.injEq] at ha
        subst ha
        apply rowFrom_replace
        exact rowFrom_same hr
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨wide, _, ha⟩ := ha
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact rowFrom_erase _
    | some row =>
      simp [hr, ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨v1, hv1, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply rowFrom_replace
      refine Or.inl ⟨row, hr, rfl, rfl, rfl, rfl, Or.inl rfl, fun x hx => ?_⟩
      rw [push_val_any hv1, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · have hsub : x ∈ row.facts.val := by
          cases wide
          · simp only [Bool.false_eq_true, if_false, world.drop_slot] at hvf
            rw [drop_slot_ok hvf, List.mem_filter] at hx; exact hx.1
          · simp only [if_true, world.drop_name] at hvf
            rw [drop_name_ok hvf, List.mem_filter] at hx; exact hx.1
        exact Or.inl ⟨row, hr, hsub⟩
      · exact Or.inr ⟨rfl, who, rfl, Or.inl ⟨value, hkd⟩⟩
  case FactUpdate who nm lt fr tv =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact rowFrom_erase _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨o1, ho1, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply rowFrom_replace
      refine Or.inl ⟨row, hr, rfl, rfl, rfl, rfl, Or.inl rfl, fun x hx => ?_⟩
      cases o1 with
      | none =>
        simp only [ok.injEq] at hvf; subst hvf
        exact Or.inl ⟨row, hr, hx⟩
      | some i =>
        obtain ⟨_, ho1', hlt⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
          (slot_index_spec row.facts.deref nm lt)
        rw [ho1] at ho1'
        simp only [ok.injEq] at ho1'
        subst ho1'
        obtain ⟨hi, hin⟩ := hlt.1 i rfl
        have hi' : i.val < row.facts.val.length := by simpa [alloc.vec.Vec.deref] using hi
        simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize] at hvf
        simp [hi'] at hvf
        subst hvf
        simp only [alloc.vec.Vec.set_val_eq, List.set_set] at hx
        rcases List.mem_or_eq_of_mem_set hx with hx | hx
        · exact Or.inl ⟨row, hr, hx⟩
        · subst hx
          have hs : slotOf (row.facts.val)[i.val] = (nm, lt) := by
            simpa [inSlot, alloc.vec.Vec.deref] using hin
          have hn : (row.facts.val)[i.val].name = nm := congrArg Prod.fst hs
          have hl : (row.facts.val)[i.val].linked_to = lt := congrArg Prod.snd hs
          refine Or.inr ⟨rfl, who, rfl, Or.inr ⟨row, _, fr, tv, hr, List.getElem_mem hi', ?_, ?_⟩⟩
          · simp [slotOf]
          · simp [hn, hl, hkd]
  case FactEnd who nm lt =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact rowFrom_erase _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply rowFrom_replace
      refine Or.inl ⟨row, hr, rfl, rfl, rfl, rfl, Or.inl rfl, fun x hx => ?_⟩
      rw [drop_slot_ok hvf, List.mem_filter] at hx
      exact Or.inl ⟨row, hr, hx.1⟩


/-! ## What a commit does to the history and the tick -/

theorem commit_facts {w w' : World} {t : time.Tick} {k : EventKind} {id : time.EventId}
    (hc : World.commit w t k = ok (id, w')) :
    id.val = w.history.val.length ∧ w'.history.val = w.history.val ++ [⟨id, t, k⟩] ∧
      w'.tick.val = max w.tick.val t.val := by
  obtain ⟨hn, hp, _⟩ := commit_ok hc
  refine ⟨?_, push_val hp, ?_⟩
  · unfold EventHistory.next_id at hn
    simp only [lift, bind_tc_ok, ok.injEq] at hn
    subst hn
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
    · rfl
    · rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h]
  · unfold World.commit at hc
    rw [hn] at hc
    simp only [bind_tc_ok] at hc
    cases ha : World.apply w.entities w.vocabulary ⟨id, t, k⟩ <;> rw [ha] at hc
    case ret bm =>
      simp only [bind_tc_ok, EventHistory.append] at hc
      rw [hp] at hc
      simp only [bind_tc_ok, time.Tick.Insts.CoreCmpPartialOrdTick.gt] at hc
      split at hc <;> simp only [ok.injEq, Prod.mk.injEq] at hc <;> obtain ⟨_, hw⟩ := hc <;>
        rw [← hw]
      · rename_i hgt _
        have : w.tick.val < t.val := by simpa using hgt
        show t.val = _; omega
      · rename_i hgt _
        have : ¬ w.tick.val < t.val := by simpa using hgt
        show w.tick.val = _; omega
    all_goals simp at hc


/-! ## Every key stays, with its type -/

theorem key_stays {m m' : ids.Ids Entity} {v : FactVocabulary} {ev : Event}
    (ha : World.apply m v ev = ok m') {k : Nat} {e : Entity}
    (h : (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e) :
    ∃ e', (m' : Std.ExtTreeMap Nat Entity compare)[k]? = some e' ∧
      e'.entity_type = e.entity_type ∧ e'.id = e.id := by
  have hk : holds m k := by
    unfold holds; rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, h]; rfl
  have hk' := apply_keeps_ids m v ev m' ha k hk
  unfold holds at hk'
  rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hk'
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hk'
  refine ⟨e', he', ?_⟩
  rcases apply_shape m v ev m' ha k e' he' with ⟨e0, h0, hid, hty, _⟩ | ⟨hn, _⟩
  · rw [h] at h0; simp only [Option.some.injEq] at h0; subst h0; exact ⟨hty, hid⟩
  · rw [h] at hn; cases hn

/-! ## Invariant 9: every link obeys the type map -/

def typesOk (v : FactVocabulary) (m : ids.Ids Entity) : Prop :=
  ∀ (k : Nat) (e : Entity) (x : Fact) (t : time.EntityId),
    (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e → x ∈ e.facts.val →
    x.linked_to = some t → t ≠ e.id ∧ ∃ e2 r,
      (m : Std.ExtTreeMap Nat Entity compare)[t.val]? = some e2 ∧
      (v.names : names.Names FactRules)[x.name]? = some r ∧
      (takesT r = true → FactRules.type_allowed r e.entity_type e2.entity_type = ok true)

/-- What a clean gate says about the link of a start. -/
def linkClean (w : World) : EventKind → Prop
  | .FactStart who nm _ (some tgt) =>
    ∀ row, (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? = some row →
      tgt ≠ who ∧ ∃ e2 r, (w.entities : Std.ExtTreeMap Nat Entity compare)[tgt.val]? = some e2 ∧
        (w.vocabulary.names : names.Names FactRules)[nm]? = some r ∧
        (takesT r = true → FactRules.type_allowed r row.entity_type e2.entity_type = ok true)
  | _ => True

theorem validate_link {w : World} {t : time.Tick} {k : EventKind}
    {f : alloc.vec.Vec reject.Rejection}
    (h : validate.validate w t k = ok f) (he : f.val = []) : linkClean w k := by
  unfold validate.validate at h
  rw [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out, _, h⟩ := h
  cases k with
  | FactStart who nm value lt =>
    cases lt with
    | none => trivial
    | some tgt => exact fun row hrow => start_link_clean h he hrow
  | _ => trivial

theorem apply_types (w : World) (ev : Event) (m' : ids.Ids Entity)
    (h : typesOk w.vocabulary w.entities) (hk : keyId w.entities)
    (hc : linkClean w ev.kind) (ha : World.apply w.entities w.vocabulary ev = ok m') :
    typesOk w.vocabulary m' := by
  intro k e' x t hk' hx hxt
  -- The target keeps its key and its type.
  have target : ∀ e2 r, (w.entities : Std.ExtTreeMap Nat Entity compare)[t.val]? = some e2 →
      (w.vocabulary.names : names.Names FactRules)[x.name]? = some r →
      ∀ ty, (takesT r = true → FactRules.type_allowed r ty e2.entity_type = ok true) →
      ∃ e2 r, (m' : Std.ExtTreeMap Nat Entity compare)[t.val]? = some e2 ∧
        (w.vocabulary.names : names.Names FactRules)[x.name]? = some r ∧
        (takesT r = true → FactRules.type_allowed r ty e2.entity_type = ok true) := by
    intro e2 r he2 hr ty hty
    obtain ⟨e2', he2', hty2, _⟩ := key_stays ha he2
    exact ⟨e2', r, he2', hr, by rw [hty2]; exact hty⟩
  rcases apply_shape w.entities w.vocabulary ev m' ha k e' hk' with
    ⟨e, he, hid, hty, _, _, _, hfacts⟩ | ⟨_, _, _, _, _, _, rfl⟩
  · rw [hid, hty]
    rcases hfacts x hx with ⟨e0, he0, hx0⟩ | ⟨_, who, hwho, hnew⟩
    · rw [he] at he0; simp only [Option.some.injEq] at he0; subst he0
      obtain ⟨hne, e2, r, he2, hr, hall⟩ := h k e x t he hx0 hxt
      exact ⟨hne, target e2 r he2 hr _ hall⟩
    · rcases hnew with ⟨val, hkd⟩ | ⟨e0, y, _, _, he0, hy, hsl, _⟩
      · rw [hkd, hxt] at hc
        have hwk : who.val = k := hwho
        obtain ⟨hne, e2, r, he2, hr, hall⟩ := hc e (by rw [hwk]; exact he)
        have heid : e.id = who := UScalar.eq_of_val_eq (by rw [hk k e he, hwk])
        refine ⟨by rw [heid]; exact hne, target e2 r he2 hr _ hall⟩
      · rw [he] at he0; simp only [Option.some.injEq] at he0; subst he0
        have hyl : y.linked_to = some t := by rw [← hxt]; exact congrArg Prod.snd hsl
        have hyn : y.name = x.name := congrArg Prod.fst hsl
        obtain ⟨hne, e2, r, he2, hr, hall⟩ := h k e y t he hy hyl
        rw [hyn] at hr
        exact ⟨hne, target e2 r he2 hr _ hall⟩
  · simp [alloc.vec.Vec.new] at hx

/-! ## Invariant 4: every `opened` points inside the history -/

def openedOk (m : ids.Ids Entity) (n : Nat) : Prop :=
  ∀ (k : Nat) (e : Entity) (x : Fact), (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e →
    x ∈ e.facts.val → x.opened.val < n

theorem apply_opened {m m' : ids.Ids Entity} {v : FactVocabulary} {ev : Event} {n : Nat}
    (h : openedOk m n) (hid : ev.id.val = n) (ha : World.apply m v ev = ok m') :
    openedOk m' (n + 1) := by
  intro k e' x hk' hx
  rcases apply_shape m v ev m' ha k e' hk' with ⟨e, he, _, _, _, _, _, hfacts⟩ | ⟨_, _, _, _, _, _, rfl⟩
  · rcases hfacts x hx with ⟨e0, he0, hx0⟩ | ⟨hop, _⟩
    · have := h k e0 x he0 hx0; omega
    · rw [hop, hid]; omega
  · simp [alloc.vec.Vec.new] at hx

/-! ## Invariant 5: a span never ends before it starts -/

def spanOk (m : ids.Ids Entity) (T : Nat) : Prop :=
  ∀ (k : Nat) (e : Entity), (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e →
    e.existence.from.val ≤ T ∧ ∀ u, e.existence.until = some u → e.existence.from.val ≤ u.val

theorem apply_span {m m' : ids.Ids Entity} {v : FactVocabulary} {ev : Event} {T : Nat}
    (h : spanOk m T) (ht : T ≤ ev.tick.val) (ha : World.apply m v ev = ok m') :
    spanOk m' (max T ev.tick.val) := by
  intro k e' hk'
  rcases apply_shape m v ev m' ha k e' hk' with
    ⟨e, he, _, _, _, hfrom, huntil, _⟩ | ⟨_, _, _, _, _, _, rfl⟩
  · obtain ⟨h1, h2⟩ := h k e he
    rw [hfrom]
    refine ⟨by omega, fun u hu => ?_⟩
    rcases huntil with hsame | ⟨_, hnew⟩
    · rw [hsame] at hu; exact h2 u hu
    · rw [hnew] at hu; simp only [Option.some.injEq] at hu; subst hu; omega
  · refine ⟨?_, ?_⟩ <;> simp <;> omega

/-! ## Invariant 11: every entity has exactly one creation event -/

/-- Does the event create the entity at key `k`? -/
def isCreate (k : Nat) (ev : Event) : Bool :=
  match ev.kind with
  | .EntityCreated id _ _ => decide (id.val = k)
  | _ => false

def createdOk (m : ids.Ids Entity) (hist : List Event) : Prop :=
  ∀ k, hist.countP (isCreate k) = if k ∈ (m : Std.ExtTreeMap Nat Entity compare) then 1 else 0

/-- What a clean gate says about a creation. -/
def createClean (w : World) : EventKind → Prop
  | .EntityCreated id _ _ => (w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]? = none
  | _ => True

theorem validate_create {w : World} {t : time.Tick} {k : EventKind}
    {f : alloc.vec.Vec reject.Rejection}
    (h : validate.validate w t k = ok f) (he : f.val = []) : createClean w k := by
  cases k with
  | EntityCreated id ty nm => exact validate_created h he
  | _ => trivial

theorem apply_created {m m' : ids.Ids Entity} {v : FactVocabulary} {ev : Event}
    {hist : List Event} (h : createdOk m hist) (hc : ∀ id ty nm,
      ev.kind = .EntityCreated id ty nm → (m : Std.ExtTreeMap Nat Entity compare)[id.val]? = none)
    (ha : World.apply m v ev = ok m') : createdOk m' (hist ++ [ev]) := by
  intro k
  rw [List.countP_append, h k]
  have hmem : ∀ j, j ∈ (m : Std.ExtTreeMap Nat Entity compare) →
      j ∈ (m' : Std.ExtTreeMap Nat Entity compare) := fun j hj => apply_keeps_ids m v ev m' ha j hj
  -- A key of `m'` is a key of `m`, or the key of this creation.
  have hback : ∀ j, j ∈ (m' : Std.ExtTreeMap Nat Entity compare) →
      j ∈ (m : Std.ExtTreeMap Nat Entity compare) ∨ isCreate j ev = true := by
    intro j hj
    rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hj
    obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hj
    rcases apply_shape m v ev m' ha j e' he' with ⟨e, he, _⟩ | ⟨_, id, _, _, hid, hkd, _⟩
    · left; rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, he]; rfl
    · right; simp [isCreate, hkd, hid]
  cases hcr : isCreate k ev
  · simp only [List.countP_cons, List.countP_nil, hcr, Bool.false_eq_true, if_false, Nat.add_zero]
    by_cases hk : k ∈ (m : Std.ExtTreeMap Nat Entity compare)
    · simp [hk, hmem k hk]
    · have : k ∉ (m' : Std.ExtTreeMap Nat Entity compare) := fun h' => by
        rcases hback k h' with h1 | h1
        · exact hk h1
        · rw [hcr] at h1; cases h1
      simp [hk, this]
  · simp only [List.countP_cons, List.countP_nil, hcr, if_true, Nat.zero_add]
    unfold isCreate at hcr
    split at hcr
    · rename_i id ty nm hkd
      have hid : id.val = k := by simpa using hcr
      have hnone := hc id ty nm hkd
      rw [hid] at hnone
      have hk : k ∉ (m : Std.ExtTreeMap Nat Entity compare) := by
        rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hnone]; simp
      -- A new key: `apply` inserts it.
      have hk' : k ∈ (m' : Std.ExtTreeMap Nat Entity compare) := by
        unfold World.apply at ha
        rw [hkd] at ha
        simp only [ids.Ids.contains, bind_tc_ok] at ha
        have : Std.ExtTreeMap.contains m id.val = false := by
          rw [hid]
          cases hc' : Std.ExtTreeMap.contains m k
          · rfl
          · exact absurd (Std.ExtTreeMap.contains_iff_mem.1 hc') hk
        simp only [this, Bool.false_eq_true, if_false, alloc.string.String.Insts.CoreCloneClone.clone,
          time.TimeSpan.open, ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
        subst ha
        rw [Std.ExtTreeMap.mem_insert]; left; simp [hid]
      simp [hk, hk']
    · cases hcr

/-! ## Invariant 12: the ticks of the history never fall -/

def ticksOk (hist : List Event) (T : Nat) : Prop :=
  hist.Pairwise (fun a b => a.tick.val ≤ b.tick.val) ∧ ∀ ev ∈ hist, ev.tick.val ≤ T

theorem ticks_step {hist : List Event} {T : Nat} {ev : Event} (h : ticksOk hist T)
    (ht : T ≤ ev.tick.val) : ticksOk (hist ++ [ev]) (max T ev.tick.val) := by
  obtain ⟨hs, hle⟩ := h
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨hs, by simp, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb
    have := hle a ha; omega
  · intro e he
    rw [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · have := hle e he; omega
    · omega


/-! ## Invariant 1: the second fold -/

abbrev SlotT := String × Option Std.I64 × Option time.EntityId × time.EventId

/-- The referee slot of a fact. -/
def slotT (x : Fact) : SlotT := (x.name, x.value, x.linked_to, x.opened)

theorem optEq_id (a b : Option time.EntityId) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq time.EntityId.Insts.CoreCmpPartialEqEntityId a b =
      ok (decide (a = b)) := by
  cases a <;> cases b <;>
    simp [core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      time.EntityId.Insts.CoreCmpPartialEqEntityId, time.EntityId.Insts.CoreCmpPartialEqEntityId.eq]

/-- A clash of a start or an end with a slot. -/
def clashB (nm : String) (lt : Option time.EntityId) (wide : Bool) (sl : SlotT) : Bool :=
  if wide then decide (sl.1 = nm) else decide (sl.1 = nm) && decide (sl.2.2.1 = lt)

theorem push_ok {T : Type} (v : alloc.vec.Vec T) (x : T) (h : v.val.length + 1 ≤ Usize.max) :
    ∃ r, alloc.vec.Vec.push v x = ok r ∧ r.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push
  dsimp only
  rw [dif_pos (by simp [h])]
  exact ⟨_, rfl, by simp [alloc.vec.Vec.from_val]⟩

theorem keep_slot_eq (kept : alloc.vec.Vec SlotT) (sl : SlotT) (nm : String)
    (lt : Option time.EntityId) (wide : Bool) (h : kept.val.length + 1 ≤ Usize.max) :
    ∃ r, verify.keep_slot kept sl nm lt wide = ok r ∧
      r.val = kept.val ++ (if clashB nm lt wide sl then [] else [sl]) := by
  obtain ⟨s, o, o1, ei⟩ := sl
  unfold verify.keep_slot
  cases wide <;> by_cases hs : s = nm <;> by_cases hl : o1 = lt <;>
    simp [alloc.string.String.Insts.CoreCmpPartialEqString.eq, optEq_id, hs, hl, clashB,
      alloc.string.String.Insts.CoreCloneClone.clone] <;>
    exact push_ok kept _ h

theorem kept_slots_loop_ok (s : Slice SlotT) (nm : String) (lt : Option time.EntityId)
    (wide : Bool) :
    ∀ (n : Nat) (kept : alloc.vec.Vec SlotT) (i : Usize), s.length - i.val = n →
      kept.val.length ≤ i.val →
      ∃ r, verify.kept_slots_loop s nm lt wide kept i = ok r ∧
        r.val = kept.val ++ (s.val.drop i.val).filter (fun sl => !clashB nm lt wide sl) := by
  intro n
  induction n with
  | zero =>
    intro kept i hn hk
    rw [verify.kept_slots_loop]
    have hge : ¬ i < Slice.len s := by scalar_tac
    simp only [hge, if_false]
    have hle : s.val.length ≤ i.val := by scalar_tac
    exact ⟨kept, rfl, by simp [List.drop_eq_nil_of_le hle]⟩
  | succ n ih =>
    intro kept i hn hk
    rw [verify.kept_slots_loop]
    have hc : i < Slice.len s := by scalar_tac
    have hlt : i.val < s.val.length := by scalar_tac
    simp only [hc, if_true]
    obtain ⟨x, hx, hxv⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (Slice.index_usize_spec s i (by simpa using hlt))
    rw [hx]
    subst hxv
    simp only [bind_tc_ok]
    have hmax : kept.val.length + 1 ≤ Usize.max := by
      have := s.property; scalar_tac
    obtain ⟨k1, hk1, hk1v⟩ := keep_slot_eq kept s.val[i.val] nm lt wide hmax
    rw [hk1]
    simp only [bind_tc_ok]
    obtain ⟨i2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hval' : i2.val = i.val + 1 := by simpa using hval
    rw [hadd]
    simp only [bind_tc_ok]
    have hk1l : k1.val.length ≤ i2.val := by
      rw [hk1v, hval']; split <;> simp <;> omega
    obtain ⟨r, hr, hrv⟩ := ih k1 i2 (by scalar_tac) hk1l
    refine ⟨r, hr, ?_⟩
    rw [hrv, hk1v, hval', List.drop_eq_getElem_cons hlt, List.filter_cons]
    split <;> simp_all

theorem kept_slots_ok (s : Slice SlotT) (nm : String) (lt : Option time.EntityId) (wide : Bool) :
    ∃ r, verify.kept_slots s nm lt wide = ok r ∧
      r.val = s.val.filter (fun sl => !clashB nm lt wide sl) := by
  obtain ⟨r, hr, hrv⟩ := kept_slots_loop_ok s nm lt wide _ (alloc.vec.Vec.new SlotT) 0#usize rfl
    (by simp [alloc.vec.Vec.new])
  exact ⟨r, hr, by simpa [alloc.vec.Vec.new] using hrv⟩

/-- An update of the matching slots. -/
def updT (nm : String) (lt : Option time.EntityId) (tv : Std.I64) (id : time.EventId)
    (sl : SlotT) : SlotT :=
  if sl.1 = nm ∧ sl.2.2.1 = lt then (sl.1, some tv, sl.2.2.1, id) else sl

theorem update_slot_eq (sl : SlotT) (nm : String) (lt : Option time.EntityId) (tv : Std.I64)
    (id : time.EventId) : verify.update_slot sl nm lt tv id = ok (updT nm lt tv id sl) := by
  obtain ⟨s, o, o1, ei⟩ := sl
  unfold verify.update_slot
  by_cases hs : s = nm <;> by_cases hl : o1 = lt <;>
    simp [alloc.string.String.Insts.CoreCmpPartialEqString.eq, optEq_id, hs, hl, updT]

theorem take_set_map {α : Type} (f : α → α) :
    ∀ (l : List α) (j : Nat) (hj : j < l.length),
      (l.set j (f l[j])).take (j + 1) ++ ((l.set j (f l[j])).drop (j + 1)).map f =
        l.take j ++ (l.drop j).map f
  | [], _, hj => by simp at hj
  | x :: t, 0, _ => by simp
  | x :: t, j + 1, hj => by
    have := take_set_map f t j (by simpa using hj)
    simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ,
      List.cons_append] at this ⊢
    rw [this]

theorem update_loop_ok (ei : time.EventId) (nm : String) (lt : Option time.EntityId) (tv : Std.I64) :
    ∀ (n : Nat) (row : verify.Row) (j : Usize), row.slots.length - j.val = n →
      ∃ v, verify.refold_one_loop ei nm lt tv row j = ok (row.kind, row.name, row.from, row.until, v) ∧
        v.val = row.slots.val.take j.val ++ (row.slots.val.drop j.val).map (updT nm lt tv ei) := by
  intro n
  induction n with
  | zero =>
    intro row j hn
    rw [verify.refold_one_loop]
    have hge : ¬ j < alloc.vec.Vec.len row.slots := by scalar_tac
    simp only [hge, if_false]
    have hle : row.slots.val.length ≤ j.val := by scalar_tac
    exact ⟨row.slots, rfl, by simp [List.drop_eq_nil_of_le hle, List.take_of_length_le hle]⟩
  | succ n ih =>
    intro row j hn
    rw [verify.refold_one_loop]
    have hc : j < alloc.vec.Vec.len row.slots := by scalar_tac
    have hlt : j.val < row.slots.val.length := by scalar_tac
    simp only [hc, if_true, Aeneas.Std.alloc.vec.Vec.index_mut_slice_index]
    obtain ⟨⟨x, back⟩, hx, hx1, hx2⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (Aeneas.Std.alloc.vec.Vec.index_mut_usize_spec row.slots j (by simpa using hlt))
    rw [hx]
    subst hx1 hx2
    simp only [bind_tc_ok, update_slot_eq]
    obtain ⟨j1, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := j) (y := 1#usize) (by scalar_tac))
    rw [hadd]
    simp only [bind_tc_ok]
    obtain ⟨v, hv, hvv⟩ := ih { row with slots := row.slots.set j (updT nm lt tv ei row.slots.val[j.val]) } j1
      (by simp; scalar_tac)
    refine ⟨v, hv, ?_⟩
    have hval' : j1.val = j.val + 1 := by simpa using hval
    rw [hvv, hval']
    simp only [alloc.vec.Vec.set_val_eq]
    exact take_set_map _ _ _ hlt


/-! ## One event keeps the rows equal to the entities -/

/-- A referee row holds exactly the entity. -/
def rowMatch (r : verify.Row) (e : Entity) : Prop :=
  r.kind = e.entity_type ∧ r.name = e.name ∧ r.from = e.existence.from ∧
    r.until = e.existence.until ∧ r.slots.val = e.facts.val.map slotT

/-- The referee rows hold exactly the entities, key by key. -/
def rowsMatch (rows : ids.Ids verify.Row) (m : ids.Ids Entity) : Prop :=
  ∀ k : Nat, Option.Rel rowMatch ((rows : Std.ExtTreeMap Nat verify.Row compare)[k]?)
    ((m : Std.ExtTreeMap Nat Entity compare)[k]?)

theorem rm_erase {rows : ids.Ids verify.Row} {m : ids.Ids Entity} (h : rowsMatch rows m) (k : Nat) :
    rowsMatch (Std.ExtTreeMap.erase rows k) (Std.ExtTreeMap.erase m k) := by
  intro j
  rw [Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_erase]
  split
  · exact Option.Rel.none
  · exact h j

theorem rm_insert {rows : ids.Ids verify.Row} {m : ids.Ids Entity} (h : rowsMatch rows m) (k : Nat)
    {r : verify.Row} {e : Entity} (hre : rowMatch r e) :
    rowsMatch (Std.ExtTreeMap.insert rows k r) (Std.ExtTreeMap.insert m k e) := by
  intro j
  rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_insert]
  split
  · exact Option.Rel.some hre
  · exact h j

theorem rm_some {rows : ids.Ids verify.Row} {m : ids.Ids Entity} (h : rowsMatch rows m) {k : Nat}
    {e : Entity} (he : (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e) :
    ∃ r, (rows : Std.ExtTreeMap Nat verify.Row compare)[k]? = some r ∧ rowMatch r e := by
  have := h k
  rw [he] at this
  generalize (rows : Std.ExtTreeMap Nat verify.Row compare)[k]? = x at this ⊢
  cases this with
  | some hr => exact ⟨_, rfl, hr⟩

theorem rm_none {rows : ids.Ids verify.Row} {m : ids.Ids Entity} (h : rowsMatch rows m) {k : Nat}
    (he : (m : Std.ExtTreeMap Nat Entity compare)[k]? = none) :
    (rows : Std.ExtTreeMap Nat verify.Row compare)[k]? = none := by
  have := h k
  rw [he] at this
  generalize (rows : Std.ExtTreeMap Nat verify.Row compare)[k]? = x at this ⊢
  cases this
  rfl

theorem rm_contains {rows : ids.Ids verify.Row} {m : ids.Ids Entity} (h : rowsMatch rows m) (k : Nat) :
    Std.ExtTreeMap.contains rows k = Std.ExtTreeMap.contains m k := by
  have := h k
  rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, Std.ExtTreeMap.contains_eq_isSome_getElem?]
  generalize (rows : Std.ExtTreeMap Nat verify.Row compare)[k]? = x at this ⊢
  generalize (m : Std.ExtTreeMap Nat Entity compare)[k]? = y at this ⊢
  cases this <;> rfl

theorem u32_le_usize : U32.max ≤ Usize.max := by
  rw [U32.max_eq, Usize.max, Usize.numBits]
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h]

theorem push_bound {T : Type} {v v' : alloc.vec.Vec T} {x : T}
    (h : alloc.vec.Vec.push v x = ok v') : v.val.length + 1 ≤ Usize.max := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · rename_i hb
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
    rcases hb with hb | hb
    · exact le_trans hb u32_le_usize
    · exact hb
  · simp at h

theorem one_target_eq (w : World) (nm : String) :
    verify.one_target w nm = world.single_target w.vocabulary nm := by
  unfold verify.one_target world.single_target fact.Count.is_single
  rfl

theorem kept_map (l : List Fact) (nm : String) (lt : Option time.EntityId) (wide : Bool) :
    (l.map slotT).filter (fun sl => !clashB nm lt wide sl) =
      (l.filter (fun f => !clashB nm lt wide (slotT f))).map slotT := by
  rw [List.filter_map]; rfl

theorem clash_name (nm : String) (lt : Option time.EntityId) (f : Fact) :
    clashB nm lt true (slotT f) = decide (f.name = nm) := rfl

theorem clash_slot (nm : String) (lt : Option time.EntityId) (f : Fact) :
    clashB nm lt false (slotT f) = inSlot f nm lt := by
  apply Bool.eq_iff_iff.2
  simp [clashB, slotT, inSlot, slotOf]

/-- The update of the one matching slot. -/
theorem map_upd_unique (L : List SlotT) (nm : String) (lt : Option time.EntityId) (tv : Std.I64)
    (id : time.EventId) (i : Nat) (hi : i < L.length)
    (huniq : ∀ j (hj : j < L.length), j ≠ i → ¬ (L[j].1 = nm ∧ L[j].2.2.1 = lt)) :
    L.map (updT nm lt tv id) = L.set i (updT nm lt tv id L[i]) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_set]
  split
  · rename_i hji; subst hji; rfl
  · rename_i hji
    have := huniq j (by simpa using h1) (Ne.symm hji)
    simp [updT, this]


/-- ONE STEP OF THE SECOND FOLD. When the rows hold the entities, the
    referee writer and `apply` agree on one more event. -/
theorem refold_step (w : World) (rows : ids.Ids verify.Row) (m m' : ids.Ids Entity) (ev : Event)
    (hm : rowsMatch rows m) (hs : oneFactPerSlot m)
    (ha : World.apply m w.vocabulary ev = ok m') :
    ∃ rows', verify.refold_one w rows ev = ok rows' ∧ rowsMatch rows' m' := by
  unfold World.apply at ha
  cases hkd : ev.kind <;> simp only [hkd] at ha
  case EntityCreated id ty nm =>
    simp only [ids.Ids.contains, bind_tc_ok] at ha
    split at ha
    · rename_i hc
      simp only [ok.injEq] at ha; subst ha
      refine ⟨rows, ?_, hm⟩
      unfold verify.refold_one
      simp [hkd, ids.Ids.contains, rm_contains hm, hc]
    · rename_i hc
      simp only [alloc.string.String.Insts.CoreCloneClone.clone, time.TimeSpan.open,
        ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
      subst ha
      refine ⟨Std.ExtTreeMap.insert rows id.val
        { kind := ty, «name» := nm, «from» := ev.tick, «until» := none,
          slots := alloc.vec.Vec.new SlotT }, ?_, ?_⟩
      · unfold verify.refold_one
        simp [hkd, ids.Ids.contains, rm_contains hm, hc, alloc.string.String.Insts.CoreCloneClone.clone,
          ids.Ids.insert]
      · exact rm_insert hm _ ⟨rfl, rfl, rfl, rfl, by simp [alloc.vec.Vec.new]⟩
  case EntityDestroyed id =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[id.val]? with
    | none =>
      simp [hr] at ha; subst ha
      refine ⟨Std.ExtTreeMap.erase rows id.val, ?_, rm_erase hm _⟩
      unfold verify.refold_one
      simp [hkd, ids.Ids.take, rm_none hm hr]
    | some row =>
      obtain ⟨r, hrr, hk, hn, hf, hu, hsl⟩ := rm_some hm hr
      simp [hr, ids.Ids.insert] at ha
      refine ⟨Std.ExtTreeMap.insert (Std.ExtTreeMap.erase rows id.val) id.val
        { r with «until» := if r.until.isNone then some ev.tick else r.until }, ?_, ?_⟩
      · unfold verify.refold_one
        simp [hkd, ids.Ids.take, hrr, ids.Ids.insert]
        split <;> simp
      · split at ha <;> simp only [bind_tc_ok, ok.injEq] at ha <;> subst ha
        · rename_i hnone
          have : r.until.isNone = true := by rw [hu, hnone]; rfl
          simp only [this, if_true]
          exact rm_insert (rm_erase hm _) _ ⟨hk, hn, hf, rfl, hsl⟩
        · rename_i hnone
          have : r.until.isNone = false := by
            rw [hu]
            cases hx : row.existence.until with
            | none => exact absurd hx hnone
            | some _ => rfl
          simp only [this, Bool.false_eq_true, if_false]
          exact rm_insert (rm_erase hm _) _ ⟨hk, hn, hf, hu, hsl⟩
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨wide, hwide, ha⟩ := ha
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none =>
      simp [hr] at ha; subst ha
      refine ⟨Std.ExtTreeMap.erase rows who.val, ?_, rm_erase hm _⟩
      unfold verify.refold_one
      simp [hkd, one_target_eq, hwide, ids.Ids.take, rm_none hm hr]
    | some row =>
      obtain ⟨r, hrr, hk, hn, hf, hu, hsl⟩ := rm_some hm hr
      simp [hr, ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨v1, hv1, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      have hvfv : vf.val = row.facts.val.filter (fun f => !clashB nm lt wide (slotT f)) := by
        cases wide
        · simp only [Bool.false_eq_true, if_false, world.drop_slot] at hvf
          rw [drop_slot_ok hvf]
          congr 1; funext f; rw [clash_slot]
        · simp only [if_true, world.drop_name] at hvf
          rw [drop_name_ok hvf]
          rfl
      obtain ⟨kept, hkept, hkv⟩ := kept_slots_ok r.slots.deref nm lt wide
      have hd : r.slots.deref.val = r.slots.val := by simp [alloc.vec.Vec.deref]
      have hkv' : kept.val = vf.val.map slotT := by
        rw [hkv, hvfv, ← kept_map, ← hsl, hd]
      obtain ⟨k1, hk1, hk1v⟩ := push_ok kept (nm, value, lt, ev.id)
        (by rw [hkv', List.length_map]; exact push_bound hv1)
      refine ⟨Std.ExtTreeMap.insert (Std.ExtTreeMap.erase rows who.val) who.val
        { r with slots := k1 }, ?_, ?_⟩
      · unfold verify.refold_one
        simp [hkd, one_target_eq, hwide, ids.Ids.take, hrr, hkept,
          alloc.string.String.Insts.CoreCloneClone.clone, hk1, ids.Ids.insert]
      · refine rm_insert (rm_erase hm _) _ ⟨hk, hn, hf, hu, ?_⟩
        show k1.val = v1.val.map slotT
        rw [hk1v, push_val_any hv1, hkv', List.map_append]
        rfl
  case FactUpdate who nm lt fr tv =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none =>
      simp [hr] at ha; subst ha
      refine ⟨Std.ExtTreeMap.erase rows who.val, ?_, rm_erase hm _⟩
      unfold verify.refold_one
      simp [hkd, ids.Ids.take, rm_none hm hr]
    | some row =>
      obtain ⟨r, hrr, hk, hn, hf, hu, hsl⟩ := rm_some hm hr
      simp [hr, ids.Ids.insert] at ha
      obtain ⟨v, hv, hvv⟩ := update_loop_ok ev.id nm lt tv _ r 0#usize rfl
      rw [bind_eq_ok] at ha
      obtain ⟨o1, ho1, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      refine ⟨Std.ExtTreeMap.insert (Std.ExtTreeMap.erase rows who.val) who.val
        { kind := r.kind, «name» := r.name, «from» := r.from, «until» := r.until, slots := v }, ?_, ?_⟩
      · unfold verify.refold_one
        simp [hkd, ids.Ids.take, hrr, hv, ids.Ids.insert]
      refine rm_insert (rm_erase hm _) _ ⟨hk, hn, hf, hu, ?_⟩
      show v.val = vf.val.map slotT
      simp at hvv
      rw [hvv, hsl]
      obtain ⟨_, ho1', hlt⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
        (slot_index_spec row.facts.deref nm lt)
      rw [ho1] at ho1'
      simp only [ok.injEq] at ho1'
      subst ho1'
      cases o1 with
      | none =>
        simp only [ok.injEq] at hvf; subst hvf
        rw [List.map_map]
        apply List.map_congr_left
        intro f hf
        have := hlt.2 rfl f (by simpa [alloc.vec.Vec.deref] using hf)
        have hn' : ¬ (f.name = nm ∧ f.linked_to = lt) := by
          simpa [inSlot, slotOf] using this
        simp [updT, slotT, hn']
      | some i =>
        obtain ⟨hi, hin⟩ := hlt.1 i rfl
        have hi' : i.val < row.facts.val.length := by simpa [alloc.vec.Vec.deref] using hi
        simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize] at hvf
        simp [hi'] at hvf
        subst hvf
        simp only [alloc.vec.Vec.set_val_eq, List.set_set, List.map_set]
        have hs' : slotOf (row.facts.val)[i.val] = (nm, lt) := by
          simpa [inSlot, alloc.vec.Vec.deref] using hin
        have hn0 : (row.facts.val)[i.val].name = nm := congrArg Prod.fst hs'
        have hl0 : (row.facts.val)[i.val].linked_to = lt := congrArg Prod.snd hs'
        rw [map_upd_unique _ nm lt tv ev.id i.val (by simpa using hi')]
        · simp [updT, slotT, hn0, hl0]
        · intro j hj hji hjs
          have hnd := hs who.val row hr
          unfold slots at hnd
          have hj' : j < row.facts.val.length := by simpa using hj
          have : (row.facts.val.map slotOf)[j]'(by simpa using hj') =
              (row.facts.val.map slotOf)[i.val]'(by simpa using hi') := by
            simp only [List.getElem_map, hs']
            simp only [List.getElem_map, slotT] at hjs
            simp [slotOf, hjs.1, hjs.2]
          exact hji ((List.Nodup.getElem_inj_iff hnd).1 this)
  case FactEnd who nm lt =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none =>
      simp [hr] at ha; subst ha
      refine ⟨Std.ExtTreeMap.erase rows who.val, ?_, rm_erase hm _⟩
      unfold verify.refold_one
      simp [hkd, ids.Ids.take, rm_none hm hr]
    | some row =>
      obtain ⟨r, hrr, hk, hn, hf, hu, hsl⟩ := rm_some hm hr
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      obtain ⟨kept, hkept, hkv⟩ := kept_slots_ok r.slots.deref nm lt false
      refine ⟨Std.ExtTreeMap.insert (Std.ExtTreeMap.erase rows who.val) who.val
        { r with slots := kept }, ?_, ?_⟩
      · unfold verify.refold_one
        simp [hkd, ids.Ids.take, hrr, hkept, ids.Ids.insert]
      refine rm_insert (rm_erase hm _) _ ⟨hk, hn, hf, hu, ?_⟩
      show kept.val = vf.val.map slotT
      rw [hkv, drop_slot_ok hvf]
      have : r.slots.deref.val = row.facts.val.map slotT := by
        rw [← hsl]; simp [alloc.vec.Vec.deref]
      rw [this, kept_map]
      congr 1
      congr 1; funext f; rw [clash_slot]


theorem refold_one_voc {w1 w2 : World} (h : w1.vocabulary = w2.vocabulary) :
    verify.refold_one w1 = verify.refold_one w2 := by
  funext rows ev
  unfold verify.refold_one
  simp only [one_target_eq, h]

/-! ## The new invariants hold in every world that proposals build -/

/-- The facts about a world that the referee reads, beyond the laws of
    the rungs before. -/
def refOk (w : World) : Prop :=
  typesOk w.vocabulary w.entities ∧ openedOk w.entities w.history.val.length ∧
    spanOk w.entities w.tick.val ∧ createdOk w.entities w.history.val ∧
    ticksOk w.history.val w.tick.val ∧
    ∃ rows, w.history.val.foldlM (verify.refold_one w) ∅ = ok rows ∧ rowsMatch rows w.entities

theorem reachP_ref (v : FactVocabulary) (w0 w : World) (h0 : World.new v = ok w0)
    (hr : ReachP w0 w) : refOk w := by
  have hw0 : w0 = ⟨0#u64, v, ∅, alloc.vec.Vec.new Event⟩ := by
    simp only [World.new, ids.Ids.new, EventHistory.new, bind_tc_ok, ok.injEq] at h0
    exact h0.symm
  induction hr with
  | refl =>
    subst hw0
    refine ⟨fun k _ _ _ hk => by simp at hk, fun k _ _ hk => by simp at hk,
      fun k _ hk => by simp at hk, fun k => by simp [alloc.vec.Vec.new],
      ⟨by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new]⟩, ∅,
      by simp [alloc.vec.Vec.new]; rfl,
      fun k => by first | simp | (simp; exact Option.Rel.none)⟩
  | @step u1 u2 t k r hr1 hp ih =>
    obtain ⟨htypes, hop, hspan, hcr, hticks, rows, hfold, hrows⟩ := ih
    cases r with
    | Err f =>
      rw [(propose_err u1 u2 t k f hp).1]
      exact ⟨htypes, hop, hspan, hcr, hticks, rows, hfold, hrows⟩
    | Ok id =>
      obtain ⟨⟨f, hvd, he⟩, hc⟩ := propose_ok u1 u2 t k id hp
      obtain ⟨_, _, hvoc⟩ := commit_ok hc
      obtain ⟨hid, hhist, htick⟩ := commit_facts hc
      have ha := commit_apply hc
      have hofps : oneFactPerSlot u1.entities :=
        every_world_one_fact_per_slot v w0 u1 h0 (reachP_reach hr1)
      have hkey : keyId u1.entities := by
        apply (reachP_holders hr1 _).2
        subst hw0
        exact ⟨fun n t _ _ _ _ _ _ _ => by simp [holdersCount, Std.ExtTreeMap.keys_eq_nil_iff.2 rfl],
          fun k _ hk => by simp at hk⟩
      have htop := validate_top hvd he
      unfold refOk
      rw [hhist, htick, hvoc]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact apply_types u1 ⟨id, t, k⟩ _ htypes hkey (validate_link hvd he) ha
      · rw [List.length_append, List.length_singleton]
        exact apply_opened hop hid ha
      · exact apply_span hspan htop ha
      · exact apply_created hcr (fun id' ty nm hk => by
          have := validate_create hvd he
          rw [show (⟨id, t, k⟩ : Event).kind = k from rfl] at hk
          subst hk; exact this) ha
      · exact ticks_step hticks htop
      · obtain ⟨rows', h1, h2⟩ := refold_step u1 rows u1.entities u2.entities ⟨id, t, k⟩ hrows hofps ha
        refine ⟨rows', ?_, h2⟩
        rw [refold_one_voc (w1 := u2) (w2 := u1) hvoc, List.foldlM_append, hfold]
        simpa using h1


/-! ## The referee, part by part -/

theorem refold_loop_eq (w : World) (evs : Slice Event) :
    ∀ (n : Nat) (rows : ids.Ids verify.Row) (i : Usize), evs.length - i.val = n →
      verify.refold_loop w evs rows i = (evs.val.drop i.val).foldlM (verify.refold_one w) rows := by
  intro n
  induction n with
  | zero =>
    intro rows i hn
    rw [verify.refold_loop]
    have hge : ¬ i < Slice.len evs := by scalar_tac
    have hle : evs.val.length ≤ i.val := by scalar_tac
    simp [hge, List.drop_eq_nil_of_le hle]
    rfl
  | succ n ih =>
    intro rows i hn
    rw [verify.refold_loop]
    have hc : i < Slice.len evs := by scalar_tac
    have hlt : i.val < evs.val.length := by scalar_tac
    simp only [hc, if_true]
    obtain ⟨x, hx, hxv⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (Slice.index_usize_spec evs i (by simpa using hlt))
    rw [hx]
    subst hxv
    obtain ⟨i2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hval' : i2.val = i.val + 1 := by simpa using hval
    rw [List.drop_eq_getElem_cons hlt, List.foldlM_cons]
    simp only [bind_tc_ok, hadd]
    congr 1
    funext rows1
    rw [ih rows1 i2 (by scalar_tac), hval']

theorem refold_eq (w : World) :
    verify.refold w = w.history.val.foldlM (verify.refold_one w) ∅ := by
  unfold verify.refold world.World.impl.history event.EventHistory.events
  simp only [ids.Ids.new, bind_tc_ok]
  rw [refold_loop_eq w _ _ ∅ 0#usize rfl]
  simp [alloc.vec.Vec.deref]

/-- Each key comes from one creation event, so the map is no larger
    than the history. -/
theorem size_le_history {m : ids.Ids Entity} {hist : List Event} (h : createdOk m hist) :
    Std.ExtTreeMap.size (m : Std.ExtTreeMap Nat Entity compare) ≤ hist.length := by
  classical
  have hex : ∀ k ∈ Std.ExtTreeMap.keys (m : Std.ExtTreeMap Nat Entity compare),
      ∃ ev ∈ hist, isCreate k ev = true := by
    intro k hk
    have := h k
    rw [if_pos (Std.ExtTreeMap.mem_keys.1 hk)] at this
    have hpos : 0 < hist.countP (isCreate k) := by omega
    obtain ⟨ev, hev, hp⟩ := List.countP_pos_iff.1 hpos
    exact ⟨ev, hev, hp⟩
  let f : Nat → Nat := fun k => hist.findIdx (isCreate k)
  have hle := Finset.card_le_card_of_injOn f
    (s := (Std.ExtTreeMap.keys (m : Std.ExtTreeMap Nat Entity compare)).toFinset)
    (t := Finset.range hist.length)
    (by
      intro k hk
      obtain ⟨ev, hev, hp⟩ := hex k (List.mem_toFinset.1 hk)
      exact Finset.mem_range.2 (List.findIdx_lt_length_of_exists ⟨ev, hev, hp⟩))
    (by
      intro k hk k' hk' hff
      obtain ⟨ev, hev, hp⟩ := hex k (List.mem_toFinset.1 hk)
      obtain ⟨ev', hev', hp'⟩ := hex k' (List.mem_toFinset.1 hk')
      have hj := List.findIdx_lt_length_of_exists ⟨ev, hev, hp⟩
      have h1 : isCreate k (hist[f k]'hj) = true := List.findIdx_getElem
      have hj' : f k' < hist.length := hff ▸ hj
      have h2 : isCreate k' (hist[f k']'hj') = true := List.findIdx_getElem
      have heq : hist[f k']'hj' = hist[f k]'hj := by simp [hff]
      rw [heq] at h2
      generalize hist[f k]'hj = e at h1 h2
      unfold isCreate at h1 h2
      split at h1 <;> simp_all)
  rw [List.toFinset_card_of_nodup Std.ExtTreeMap.nodup_keys, Std.ExtTreeMap.length_keys,
    Finset.card_range] at hle
  exact hle

theorem size_lt {m : ids.Ids Entity} {hist : alloc.vec.Vec Event} (h : createdOk m hist.val) :
    Std.ExtTreeMap.size (m : Std.ExtTreeMap Nat Entity compare) < 2 ^ UScalarTy.Usize.numBits := by
  have h1 := size_le_history h
  have h2 := hist.property
  have h3 : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    rw [Usize.max, Usize.numBits]; have := Nat.two_pow_pos UScalarTy.Usize.numBits; omega
  omega

theorem len_eq {V : Type} (m : ids.Ids V)
    (h : Std.ExtTreeMap.size (m : Std.ExtTreeMap Nat V compare) < 2 ^ UScalarTy.Usize.numBits) :
    ∃ n : Usize, ids.Ids.len m = ok n ∧ n.val = Std.ExtTreeMap.size (m : Std.ExtTreeMap Nat V compare) := by
  unfold ids.Ids.len
  rw [dif_pos h]
  exact ⟨_, rfl, by simp⟩

theorem rows_size {rows : ids.Ids verify.Row} {m : ids.Ids Entity} (h : rowsMatch rows m) :
    Std.ExtTreeMap.size (rows : Std.ExtTreeMap Nat verify.Row compare) =
      Std.ExtTreeMap.size (m : Std.ExtTreeMap Nat Entity compare) := by
  rw [← Std.ExtTreeMap.length_keys, ← Std.ExtTreeMap.length_keys]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup Std.ExtTreeMap.nodup_keys Std.ExtTreeMap.nodup_keys]
  intro k
  rw [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_iff_isSome_getElem?,
    Std.ExtTreeMap.mem_iff_isSome_getElem?]
  have := h k
  generalize (rows : Std.ExtTreeMap Nat verify.Row compare)[k]? = x at this ⊢
  generalize (m : Std.ExtTreeMap Nat Entity compare)[k]? = y at this ⊢
  cases this <;> simp

/-- The ids of the map: every key, when each key is below `2^32`. -/
theorem ids_eq {m : ids.Ids Entity} (hk : keyId m)
    (hs : Std.ExtTreeMap.size (m : Std.ExtTreeMap Nat Entity compare) < 2 ^ UScalarTy.Usize.numBits) :
    ∃ v, ids.Ids.ids m = ok v ∧ v.val = idsOf m ∧
      ∀ id ∈ v.val, ∃ e, (m : Std.ExtTreeMap Nat Entity compare)[id.val]? = some e := by
  unfold ids.Ids.ids
  have hlen : (idsOf m).length ≤ Usize.max := by
    have : (idsOf m).length ≤ (Std.ExtTreeMap.keys (m : Std.ExtTreeMap Nat Entity compare)).length :=
      List.length_filterMap_le _ _
    rw [Std.ExtTreeMap.length_keys] at this
    have h3 : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by rw [Usize.max, Usize.numBits]
    omega
  simp only [idsOf] at hlen
  dsimp only
  rw [dif_pos hlen]
  refine ⟨_, rfl, by simp [alloc.vec.Vec.from_val, idsOf], fun id hid => ?_⟩
  simp only [alloc.vec.Vec.from_val, List.mem_filterMap] at hid
  obtain ⟨k, hkm, hid⟩ := hid
  split at hid
  · simp only [Option.some.injEq] at hid
    subst hid
    rw [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_iff_isSome_getElem?] at hkm
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hkm
    exact ⟨e, by simpa using he⟩
  · cases hid


theorem same_slot_true (x : Fact) : verify.same_slot (slotT x) x = ok true := by
  unfold verify.same_slot slotT
  cases hv : x.value <;> cases hl : x.linked_to <;>
    simp [alloc.string.String.Insts.CoreCmpPartialEqString.eq, optEq_id, hv, hl,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.cmp.PartialEqI64, liftFun2,
      core.cmp.impls.PartialEqI64.eq, time.EventId.Insts.CoreCmpPartialEqEventId.eq,
      time.EntityId.Insts.CoreCmpPartialEqEntityId.eq]

theorem same_row_loop_true (facts : alloc.vec.Vec Fact) (slots : alloc.vec.Vec SlotT)
    (h : slots.val = facts.val.map slotT) :
    ∀ (n : Nat) (i : Usize), slots.length - i.val = n →
      verify.same_row_loop facts slots i = ok true := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [verify.same_row_loop]
    have hge : ¬ i < alloc.vec.Vec.len slots := by scalar_tac
    simp [hge]
  | succ n ih =>
    intro i hn
    rw [verify.same_row_loop]
    have hc : i < alloc.vec.Vec.len slots := by scalar_tac
    have hlt : i.val < slots.val.length := by scalar_tac
    have hlf : i.val < facts.val.length := by rw [h, List.length_map] at hlt; exact hlt
    have hsl : slots.val[i.val] = slotT facts.val[i.val] := by simp [h]
    simp [hc, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hlt,
      List.getElem?_eq_getElem hlf, hsl, same_slot_true]
    obtain ⟨i2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [hadd]
    simp only [bind_tc_ok]
    exact ih i2 (by scalar_tac)

theorem same_row_true {w : World} {rows : ids.Ids verify.Row} (hm : rowsMatch rows w.entities)
    (hk : keyId w.entities) {key : time.EntityId} {e : Entity}
    (he : (w.entities : Std.ExtTreeMap Nat Entity compare)[key.val]? = some e) :
    verify.same_row w rows key = ok true := by
  have hid : e.id.val = key.val := hk _ e he
  obtain ⟨r, hr, hkd, hn, hf, hu, hsl⟩ := rm_some hm he
  have hr' : (rows : Std.ExtTreeMap Nat verify.Row compare)[e.id.val]? = some r := by rw [hid]; exact hr
  unfold verify.same_row
  simp only [entity_eq, he, ids.Ids.get, hr', bind_tc_ok, hkd, hn, hf, hu,
    entity.EntityType.Insts.CoreCmpPartialEqEntityType.ne, bne_self_eq_false,
    alloc.string.String.Insts.CoreCmpPartialEqString.ne, time.Tick.Insts.CoreCmpPartialEqTick.ne,
    core.option.Option.Insts.CoreCmpPartialEqOption.ne, ne_eq, not_true_eq_false, decide_false,
    Bool.false_eq_true, if_false]
  have hopt : core.option.Option.Insts.CoreCmpPartialEqOption.eq time.Tick.Insts.CoreCmpPartialEqTick
      e.existence.until e.existence.until = ok true := by
    cases e.existence.until <;>
      simp [core.option.Option.Insts.CoreCmpPartialEqOption.eq, time.Tick.Insts.CoreCmpPartialEqTick,
        time.Tick.Insts.CoreCmpPartialEqTick.eq]
  rw [hopt]
  simp only [bind_tc_ok, Bool.not_true, Bool.false_eq_true, if_false]
  have hlen : (alloc.vec.Vec.len r.slots != alloc.vec.Vec.len e.facts) = false := by
    have : r.slots.val.length = e.facts.val.length := by rw [hsl, List.length_map]
    simp only [bne_eq_false_iff_eq]
    scalar_tac
  rw [hlen]
  simp only [Bool.false_eq_true, if_false]
  exact same_row_loop_true e.facts r.slots hsl _ 0#usize rfl

theorem ticks_rise_loop_true (w : World) (evs : Slice Event) :
    ∀ (n : Nat) (last : time.Tick) (i : Usize), evs.length - i.val = n →
      (evs.val.drop i.val).Pairwise (fun a b => a.tick.val ≤ b.tick.val) →
      (∀ ev ∈ evs.val.drop i.val, last.val ≤ ev.tick.val) → last.val ≤ w.tick.val →
      (∀ ev ∈ evs.val.drop i.val, ev.tick.val ≤ w.tick.val) →
      verify.ticks_rise_loop w evs last i = ok true := by
  intro n
  induction n with
  | zero =>
    intro last i hn _ _ hlast _
    rw [verify.ticks_rise_loop]
    have hge : ¬ i < Slice.len evs := by scalar_tac
    simp only [hge, if_false, time.Tick.Insts.CoreCmpPartialOrdTick.ge, ok.injEq,
      decide_eq_true_eq]
    show last.val ≤ w.tick.val
    exact hlast
  | succ n ih =>
    intro last i hn hp hl _ ht
    rw [verify.ticks_rise_loop]
    have hc : i < Slice.len evs := by scalar_tac
    have hlt : i.val < evs.val.length := by scalar_tac
    simp only [hc, if_true]
    obtain ⟨x, hx, hxv⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (Slice.index_usize_spec evs i (by simpa using hlt))
    rw [hx]
    subst hxv
    rw [List.drop_eq_getElem_cons hlt] at hp hl ht
    have hle := hl _ List.mem_cons_self
    have hnot : ¬ evs.val[i.val].tick < last := fun h' => by
      have : evs.val[i.val].tick.val < last.val := h'
      omega
    simp only [time.Tick.Insts.CoreCmpPartialOrdTick.lt, hnot, decide_false, bind_tc_ok,
      Bool.false_eq_true, if_false]
    obtain ⟨i2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hval' : i2.val = i.val + 1 := by simpa using hval
    rw [hadd]
    simp only [bind_tc_ok]
    rw [List.pairwise_cons] at hp
    have hd : evs.val.drop i2.val = evs.val.drop (i.val + 1) := by rw [hval']
    apply ih _ i2 (by scalar_tac) <;> (try rw [hd])
    · exact hp.2
    · exact hp.1
    · exact ht _ List.mem_cons_self
    · exact fun ev hev => ht ev (List.mem_cons_of_mem _ hev)

theorem ticks_rise_true {w : World} (h : ticksOk w.history.val w.tick.val) :
    verify.ticks_rise w = ok true := by
  unfold verify.ticks_rise world.World.impl.history event.EventHistory.events
  simp only [bind_tc_ok]
  obtain ⟨hs, hle⟩ := h
  apply ticks_rise_loop_true w _ _ 0#u64 0#usize rfl <;> simp [alloc.vec.Vec.deref]
  · exact hs
  · exact hle


theorem same_state_loop_true {w : World} {rows : ids.Ids verify.Row}
    (hm : rowsMatch rows w.entities) (hk : keyId w.entities) (ht : verify.ticks_rise w = ok true)
    (ids : alloc.vec.Vec time.EntityId)
    (hids : ∀ id ∈ ids.val, ∃ e, (w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]? = some e) :
    ∀ (n : Nat) (i : Usize), ids.length - i.val = n →
      verify.same_state_loop w rows ids i = ok true := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [verify.same_state_loop]
    have hge : ¬ i < alloc.vec.Vec.len ids := by scalar_tac
    simp [hge, ht]
  | succ n ih =>
    intro i hn
    rw [verify.same_state_loop]
    have hc : i < alloc.vec.Vec.len ids := by scalar_tac
    have hlt : i.val < ids.val.length := by scalar_tac
    obtain ⟨e, he⟩ := hids _ (List.getElem_mem hlt)
    simp [hc, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hlt, same_row_true hm hk he]
    obtain ⟨i2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [hadd]
    simp only [bind_tc_ok]
    exact ih i2 (by scalar_tac)

/-- INVARIANT 1 HOLDS. The state is the second fold of the history. -/
theorem same_state_true {w : World} {rows : ids.Ids verify.Row}
    (hm : rowsMatch rows w.entities) (hk : keyId w.entities)
    (hcr : createdOk w.entities w.history.val) (ht : ticksOk w.history.val w.tick.val) :
    verify.same_state w rows = ok true := by
  have hs := size_lt (hist := w.history) hcr
  obtain ⟨n1, h1, hv1⟩ := len_eq w.entities hs
  obtain ⟨n2, h2, hv2⟩ := len_eq rows (by rw [rows_size hm]; exact hs)
  obtain ⟨v, hv, _, hids⟩ := ids_eq hk hs
  unfold verify.same_state world.World.len world.World.entity_ids
  rw [h1, h2]
  have hne : (n1 != n2) = false := by
    simp only [bne_eq_false_iff_eq]
    apply UScalar.eq_of_val_eq
    rw [hv1, hv2, rows_size hm]
  simp only [bind_tc_ok, hne, Bool.false_eq_true, if_false, hv]
  exact same_state_loop_true hm hk (ticks_rise_true ht) v hids _ 0#usize rfl

/-! ## Invariant 11: the creation pass of `sound` -/

theorem created_once_eq (w : World) (created : ids.Ids Unit) (ev : Event)
    (h : ∀ k, isCreate k ev = true → k ∉ (created : Std.ExtTreeMap Nat Unit compare)) :
    verify.created_once w created ev =
      ok (true, match ev.kind with
        | .EntityCreated id _ _ => Std.ExtTreeMap.insert created id.val ()
        | _ => created) := by
  unfold verify.created_once
  cases hkd : ev.kind <;> simp only [hkd]
  case EntityCreated id ty nm =>
    have hn := h id.val (by simp [isCreate, hkd])
    have : Std.ExtTreeMap.contains created id.val = false := by
      cases hc : Std.ExtTreeMap.contains created id.val
      · rfl
      · exact absurd (Std.ExtTreeMap.contains_iff_mem.1 hc) hn
    simp [ids.Ids.contains, this, ids.Ids.insert]

theorem created_loop_ok (w : World) (evs : Slice Event) :
    ∀ (n : Nat) (created : ids.Ids Unit) (i : Usize), evs.length - i.val = n →
      (∀ k, (evs.val.drop i.val).countP (isCreate k) +
        (if k ∈ (created : Std.ExtTreeMap Nat Unit compare) then 1 else 0) ≤ 1) →
      ∃ c', verify.all_created_once_loop w created evs i = ok (true, c') ∧
        ∀ k, k ∈ (c' : Std.ExtTreeMap Nat Unit compare) ↔
          k ∈ (created : Std.ExtTreeMap Nat Unit compare) ∨ 0 < (evs.val.drop i.val).countP (isCreate k) := by
  intro n
  induction n with
  | zero =>
    intro created i hn _
    rw [verify.all_created_once_loop]
    have hge : ¬ i < Slice.len evs := by scalar_tac
    have hle : evs.val.length ≤ i.val := by scalar_tac
    simp only [hge, if_false]
    exact ⟨created, rfl, fun k => by simp [List.drop_eq_nil_of_le hle]⟩
  | succ n ih =>
    intro created i hn hcount
    rw [verify.all_created_once_loop]
    have hc : i < Slice.len evs := by scalar_tac
    have hlt : i.val < evs.val.length := by scalar_tac
    simp only [hc, if_true]
    obtain ⟨x, hx, hxv⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (Slice.index_usize_spec evs i (by simpa using hlt))
    rw [hx]
    subst hxv
    rw [List.drop_eq_getElem_cons hlt] at hcount
    have hnot : ∀ k, isCreate k evs.val[i.val] = true →
        k ∉ (created : Std.ExtTreeMap Nat Unit compare) := by
      intro k hk hmem
      have := hcount k
      rw [List.countP_cons, if_pos hk, if_pos hmem] at this
      omega
    simp only [bind_tc_ok]
    rw [created_once_eq w created _ hnot]
    simp only [bind_tc_ok, if_true]
    obtain ⟨i2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hval' : i2.val = i.val + 1 := by simpa using hval
    rw [hadd]
    simp only [bind_tc_ok]
    -- The set after this event.
    set c1 := (match evs.val[i.val].kind with
      | .EntityCreated id _ _ => Std.ExtTreeMap.insert created id.val ()
      | _ => created) with hc1
    have hmem1 : ∀ k, k ∈ (c1 : Std.ExtTreeMap Nat Unit compare) ↔
        k ∈ (created : Std.ExtTreeMap Nat Unit compare) ∨ isCreate k evs.val[i.val] = true := by
      intro k
      rw [hc1]
      unfold isCreate
      split
      · rename_i id _ _ _
        rw [Std.ExtTreeMap.mem_insert]
        by_cases hk : k = id.val
        · subst hk; simp
        · have : ¬ compare id.val k = .eq := by
            rw [Nat.compare_eq_eq]; exact fun h => hk h.symm
          simp [this, hk, eq_comm]
      · simp
    obtain ⟨c', hc', hmem'⟩ := ih c1 i2 (by scalar_tac) (by
      intro k
      have := hcount k
      rw [hval']
      by_cases hk : isCreate k evs.val[i.val] = true
      · have hin : k ∈ (c1 : Std.ExtTreeMap Nat Unit compare) := (hmem1 k).2 (Or.inr hk)
        simp only [List.countP_cons, hk, if_true] at this
        simp only [hin, if_true]
        omega
      · have hin : k ∈ (c1 : Std.ExtTreeMap Nat Unit compare) ↔
            k ∈ (created : Std.ExtTreeMap Nat Unit compare) := by
          rw [hmem1 k]; simp [hk]
        simp only [List.countP_cons, hk, Bool.false_eq_true, if_false, Nat.add_zero] at this
        by_cases hc2 : k ∈ (created : Std.ExtTreeMap Nat Unit compare)
        · simp only [hin.2 hc2, hc2, if_true] at this ⊢; omega
        · have : k ∉ (c1 : Std.ExtTreeMap Nat Unit compare) := fun h' => hc2 (hin.1 h')
          simp only [this, hc2, if_false] at *; omega)
    refine ⟨c', hc', fun k => ?_⟩
    rw [hmem', hval', hmem1, List.drop_eq_getElem_cons hlt, List.countP_cons]
    by_cases hk : isCreate k evs.val[i.val] = true <;> simp [hk] <;> tauto


/-! ## The checks of one fact -/

theorem slot_before_loop_false (facts : Slice Fact) (i : Usize) (hi : i.val < facts.val.length)
    (hnd : (facts.val.map slotOf).Nodup) :
    ∀ (n : Nat) (j : Usize), i.val - j.val = n →
      verify.slot_before_loop facts i j = ok false := by
  intro n
  induction n with
  | zero =>
    intro j hn
    rw [verify.slot_before_loop]
    have hge : ¬ j < i := by scalar_tac
    simp [hge]
  | succ n ih =>
    intro j hn
    rw [verify.slot_before_loop]
    have hc : j < i := by scalar_tac
    have hj : j.val < facts.val.length := by scalar_tac
    simp only [hc, if_true]
    obtain ⟨x, hx, hxv⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (Slice.index_usize_spec facts j (by simpa using hj))
    obtain ⟨y, hy, hyv⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (Slice.index_usize_spec facts i (by simpa using hi))
    rw [hx]
    simp only [bind_tc_ok]
    rw [hy]
    subst hxv hyv
    have hne : ¬ (facts.val[j.val].name = facts.val[i.val].name ∧
        facts.val[j.val].linked_to = facts.val[i.val].linked_to) := by
      intro ⟨h1, h2⟩
      have heq : (facts.val.map slotOf)[j.val]'(by simpa using hj) =
          (facts.val.map slotOf)[i.val]'(by simpa using hi) := by
        simp [slotOf, h1, h2]
      have := (List.Nodup.getElem_inj_iff hnd).1 heq
      have : j.val < i.val := hc
      omega
    obtain ⟨j2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := j) (y := 1#usize) (by scalar_tac))
    by_cases hn1 : facts.val[j.val].name = facts.val[i.val].name
    · have hl : facts.val[j.val].linked_to ≠ facts.val[i.val].linked_to := fun h => hne ⟨hn1, h⟩
      simp [alloc.string.String.Insts.CoreCmpPartialEqString.eq, hn1, optEq_id, hl, hadd]
      exact ih j2 (by scalar_tac)
    · simp [alloc.string.String.Insts.CoreCmpPartialEqString.eq, hn1, hadd]
      exact ih j2 (by scalar_tac)

theorem opened_inside_true {w : World} {f : Fact} (h : f.opened.val < w.history.val.length) :
    verify.opened_inside w f = ok true := by
  unfold verify.opened_inside world.World.impl.history event.EventHistory.len
  have hlt : f.opened.val < 2 ^ UScalarTy.Usize.numBits := by
    have := w.history.property
    have h3 : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
      rw [Usize.max, Usize.numBits]; have := Nat.two_pow_pos UScalarTy.Usize.numBits; omega
    omega
  simp only [lift, bind_tc_ok, ok.injEq, decide_eq_true_eq]
  show (UScalar.cast .Usize f.opened).val < (alloc.vec.Vec.len w.history).val
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ hlt]
  simpa using h

theorem value_fits_true {r : FactRules} {f : Fact} (h : numOk (shapeOf r) f.value) :
    verify.value_fits r f = ok true := by
  unfold verify.value_fits
  simp only [shape_eq, bind_tc_ok]
  cases hs : shapeOf r with
  | Flag d => rw [hs] at h; simp [numOk] at h; simp [h]
  | Number band d =>
    rw [hs] at h
    obtain ⟨n, hn, hb⟩ := h
    simp [hn, hb]

theorem link_fits_true {w : World} {e : Entity} {r : FactRules} {f : Fact}
    (hl : takesT r = f.linked_to.isSome)
    (ht : ∀ t, f.linked_to = some t → t ≠ e.id ∧ ∃ e2,
      (w.entities : Std.ExtTreeMap Nat Entity compare)[t.val]? = some e2 ∧
      FactRules.type_allowed r e.entity_type e2.entity_type = ok true) :
    verify.link_fits w e r f = ok true := by
  unfold verify.link_fits
  simp only [takes_target_eq, bind_tc_ok]
  cases hlt : f.linked_to with
  | none => rw [hlt] at hl; simp [hl]
  | some t =>
    rw [hlt] at hl
    obtain ⟨hne, e2, he2, hall⟩ := ht t hlt
    simp [hl, time.EntityId.Insts.CoreCmpPartialEqEntityId.eq, hne, type_of_eq, he2, hall]


/-! ## The counts of one fact -/

theorem holds_slot_loop_eq (nm : String) (t : time.EntityId) (e : Entity) :
    ∀ (n : Nat) (i : Usize), e.facts.length - i.val = n →
      verify.holds_slot_loop nm t e i = ok ((e.facts.val.drop i.val).any (fun f => inSlot f nm (some t))) := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [verify.holds_slot_loop]
    have hge : ¬ i < alloc.vec.Vec.len e.facts := by scalar_tac
    have hle : e.facts.val.length ≤ i.val := by scalar_tac
    simp [hge, List.drop_eq_nil_of_le hle]
  | succ n ih =>
    intro i hn
    rw [verify.holds_slot_loop]
    have hc : i < alloc.vec.Vec.len e.facts := by scalar_tac
    have hlt : i.val < e.facts.val.length := by scalar_tac
    obtain ⟨i2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hval' : i2.val = i.val + 1 := by simpa using hval
    have hrec := ih i2 (by scalar_tac)
    rw [hval'] at hrec
    rw [List.drop_eq_getElem_cons hlt, List.any_cons]
    by_cases hn1 : e.facts.val[i.val].name = nm <;>
      by_cases hl1 : e.facts.val[i.val].linked_to = some t <;>
      simp [hc, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hlt,
        alloc.string.String.Insts.CoreCmpPartialEqString.eq, optEq_id, hn1, hl1, hadd, hrec,
        inSlot, slotOf]

theorem holds_slot_eq (w : World) (key : time.EntityId) (nm : String) (t : time.EntityId) :
    verify.holds_slot w key nm t = ok (holdsAt w.entities nm t key.val) := by
  unfold verify.holds_slot holdsAt
  simp only [entity_eq, bind_tc_ok]
  cases he : (w.entities : Std.ExtTreeMap Nat Entity compare)[key.val]? with
  | none => rfl
  | some e =>
    simp only
    rw [holds_slot_loop_eq nm t e _ 0#usize rfl]
    rfl

theorem holders_count_loop_ok (w : World) (nm : String) (t : time.EntityId)
    (ids : alloc.vec.Vec time.EntityId) :
    ∀ (k : Nat) (n i : Usize), ids.length - i.val = k → n.val ≤ i.val →
      ∃ r, verify.holders_count_loop w nm t ids n i = ok r ∧
        r.val = n.val + (ids.val.drop i.val).countP (fun id => holdsAt w.entities nm t id.val) := by
  intro k
  induction k with
  | zero =>
    intro n i hk _
    rw [verify.holders_count_loop]
    have hge : ¬ i < alloc.vec.Vec.len ids := by scalar_tac
    have hle : ids.val.length ≤ i.val := by scalar_tac
    simp only [hge, if_false]
    exact ⟨n, rfl, by simp [List.drop_eq_nil_of_le hle]⟩
  | succ k ih =>
    intro n i hk hn
    rw [verify.holders_count_loop]
    have hc : i < alloc.vec.Vec.len ids := by scalar_tac
    have hlt : i.val < ids.val.length := by scalar_tac
    obtain ⟨i2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hval' : i2.val = i.val + 1 := by simpa using hval
    cases hb : holdsAt w.entities nm t ids.val[i.val].val
    · simp [hc, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hlt, holds_slot_eq, hb, hadd]
      obtain ⟨r, hr, hrv⟩ := ih n i2 (by scalar_tac) (by omega)
      refine ⟨r, hr, ?_⟩
      rw [hrv, hval', List.drop_eq_getElem_cons hlt, List.countP_cons, hb]
      simp
    · obtain ⟨n1, hadd1, hval1⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
        (UScalar.add_spec (x := n) (y := 1#usize) (by scalar_tac))
      have hval1' : n1.val = n.val + 1 := by simpa using hval1
      simp [hc, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hlt, holds_slot_eq, hb, hadd,
        hadd1]
      obtain ⟨r, hr, hrv⟩ := ih n1 i2 (by scalar_tac) (by omega)
      refine ⟨r, hr, ?_⟩
      rw [hrv, hval1', hval', List.drop_eq_getElem_cons hlt, List.countP_cons, hb]
      simp; omega

theorem idsOf_val {m : ids.Ids Entity} (hk : keyId m) :
    (idsOf m).map (fun id => id.val) = Std.ExtTreeMap.keys (m : Std.ExtTreeMap Nat Entity compare) := by
  unfold idsOf
  rw [List.map_filterMap]
  conv => rhs; rw [← List.filterMap_some (l := Std.ExtTreeMap.keys (m : Std.ExtTreeMap Nat Entity compare))]
  apply List.filterMap_congr
  intro k hkm
  rw [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_iff_isSome_getElem?] at hkm
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hkm
  have hid := hk k e he
  have hlt : k < 2 ^ UScalarTy.U32.numBits := by rw [← hid]; exact UScalar.hBounds e.id
  have hlt' : k < 4294967296 := by simpa using hlt
  simp [hlt']

theorem holders_count_eq {w : World} (hk : keyId w.entities)
    (hs : Std.ExtTreeMap.size (w.entities : Std.ExtTreeMap Nat Entity compare) < 2 ^ UScalarTy.Usize.numBits)
    (nm : String) (t : time.EntityId) :
    ∃ r, verify.holders_count w nm t = ok r ∧ r.val = holdersCount w.entities nm t := by
  obtain ⟨v, hv, hvv, _⟩ := ids_eq hk hs
  unfold verify.holders_count world.World.entity_ids
  simp only [hv, bind_tc_ok]
  obtain ⟨r, hr, hrv⟩ := holders_count_loop_ok w nm t v _ 0#usize 0#usize rfl (by simp)
  refine ⟨r, hr, ?_⟩
  rw [hrv, hvv, show (0#usize : Usize).val = 0 from rfl, Nat.zero_add, List.drop_zero]
  unfold holdersCount
  rw [← idsOf_val hk, List.countP_map]
  rfl


theorem first_target_loop_ok (facts : Slice Fact) (nm : String) (i : Usize) (hi : i.val < facts.val.length) :
    ∀ (n : Nat) (j : Usize), i.val - j.val = n → ∃ b, verify.first_target_loop facts nm i j = ok b := by
  intro n
  induction n with
  | zero =>
    intro j hn
    rw [verify.first_target_loop]
    have hge : ¬ j < i := by scalar_tac
    simp [hge]
  | succ n ih =>
    intro j hn
    rw [verify.first_target_loop]
    have hc : j < i := by scalar_tac
    have hj : j.val < facts.val.length := by scalar_tac
    obtain ⟨x, hx, hxv⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (Slice.index_usize_spec facts j (by simpa using hj))
    obtain ⟨y, hy, hyv⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (Slice.index_usize_spec facts i (by simpa using hi))
    obtain ⟨j2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := j) (y := 1#usize) (by scalar_tac))
    obtain ⟨b, hb⟩ := ih j2 (by scalar_tac)
    simp only [hc, if_true, hx, hy, hadd, hb, bind_tc_ok, alloc.string.String.Insts.CoreCmpPartialEqString.eq,
      optEq_id]
    split
    · split
      · exact ⟨false, rfl⟩
      · exact ⟨b, rfl⟩
    · exact ⟨b, rfl⟩

theorem first_target_ok (facts : Slice Fact) (nm : String) (i : Usize) (hi : i.val < facts.val.length) :
    ∃ b, verify.first_target facts nm i = ok b ∧ (b = true → facts.val[i.val].name = nm) := by
  unfold verify.first_target
  obtain ⟨y, hy, hyv⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
    (Slice.index_usize_spec facts i (by simpa using hi))
  subst hyv
  simp only [hy, bind_tc_ok, alloc.string.String.Insts.CoreCmpPartialEqString.ne]
  by_cases hn : facts.val[i.val].name = nm
  · simp only [hn, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
    split
    · exact ⟨false, rfl, fun h => by cases h⟩
    · obtain ⟨b, hb⟩ := first_target_loop_ok facts nm i hi _ 0#usize rfl
      exact ⟨b, hb, fun _ => by first | exact hn | trivial⟩
  · simp only [hn, ne_eq, not_false_eq_true, decide_true, if_true]
    exact ⟨false, rfl, fun h => by cases h⟩

theorem distinct_loop_le (facts : Slice Fact) (nm : String) :
    ∀ (k : Nat) (n i : Usize), facts.length - i.val = k → n.val ≤ i.val →
      ∃ r, verify.distinct_targets_loop facts nm n i = ok r ∧
        r.val ≤ n.val + (facts.val.drop i.val).countP (fun f => decide (f.name = nm)) := by
  intro k
  induction k with
  | zero =>
    intro n i hk _
    rw [verify.distinct_targets_loop]
    have hge : ¬ i < Slice.len facts := by scalar_tac
    simp only [hge, if_false]
    exact ⟨n, rfl, by omega⟩
  | succ k ih =>
    intro n i hk hn
    rw [verify.distinct_targets_loop]
    have hc : i < Slice.len facts := by scalar_tac
    have hlt : i.val < facts.val.length := by scalar_tac
    obtain ⟨b, hb, hbn⟩ := first_target_ok facts nm i hlt
    obtain ⟨i2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hval' : i2.val = i.val + 1 := by simpa using hval
    cases b
    · simp only [hc, if_true, hb, bind_tc_ok, Bool.false_eq_true, if_false, hadd]
      obtain ⟨r, hr, hrv⟩ := ih n i2 (by scalar_tac) (by omega)
      refine ⟨r, hr, ?_⟩
      rw [hval'] at hrv
      rw [List.drop_eq_getElem_cons hlt, List.countP_cons]
      split <;> omega
    · obtain ⟨n1, hadd1, hval1⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
        (UScalar.add_spec (x := n) (y := 1#usize) (by scalar_tac))
      have hval1' : n1.val = n.val + 1 := by simpa using hval1
      simp only [hc, if_true, hb, bind_tc_ok, hadd1, hadd]
      obtain ⟨r, hr, hrv⟩ := ih n1 i2 (by scalar_tac) (by omega)
      refine ⟨r, hr, ?_⟩
      rw [hval', hval1'] at hrv
      rw [List.drop_eq_getElem_cons hlt, List.countP_cons, if_pos (by simpa using hbn rfl)]
      omega

theorem holders_fit_true {w : World} (hk : keyId w.entities)
    (hs : Std.ExtTreeMap.size (w.entities : Std.ExtTreeMap Nat Entity compare) < 2 ^ UScalarTy.Usize.numBits)
    {holders : Count} {f : Fact}
    (h : ∀ L t, limitOf holders = some L → f.linked_to = some t →
      holdersCount w.entities f.name t ≤ L.val) :
    verify.holders_fit w holders f = ok true := by
  unfold verify.holders_fit
  simp only [limit_eq, bind_tc_ok]
  cases hl : limitOf holders with
  | none => rfl
  | some L =>
    cases ht : f.linked_to with
    | none => rfl
    | some t =>
      obtain ⟨r, hr, hrv⟩ := holders_count_eq hk hs f.name t
      simp only [hr, lift, bind_tc_ok, ok.injEq, decide_eq_true_eq]
      show r.val ≤ (core.convert.num.FromUsizeU16.from L).val
      rw [core.convert.num.FromUsizeU16.from_val_eq, hrv]
      exact h L t hl ht

theorem targets_fit_true {e : Entity} {targets : Count} {f : Fact}
    (h : ∀ L, limitOf targets = some L → countName e f.name ≤ L.val) :
    verify.targets_fit e targets f = ok true := by
  unfold verify.targets_fit
  simp only [limit_eq, bind_tc_ok]
  cases hl : limitOf targets with
  | none => rfl
  | some L =>
    obtain ⟨r, hr, hrv⟩ := distinct_loop_le e.facts.deref f.name _ 0#usize 0#usize rfl (by simp)
    simp only [verify.distinct_targets, hr, lift, bind_tc_ok, ok.injEq, decide_eq_true_eq]
    show r.val ≤ (core.convert.num.FromUsizeU16.from L).val
    rw [core.convert.num.FromUsizeU16.from_val_eq]
    have := h L hl
    unfold countName at this
    rw [show (0#usize : Usize).val = 0 from rfl, Nat.zero_add, List.drop_zero] at hrv
    simp only [alloc.vec.Vec.deref] at hrv
    have h2 : (Slice.from e.facts.val e.facts.property).val = e.facts.val := by simp
    rw [h2] at hrv
    omega


/-! ## One fact, one entity, and the walk -/

/-- The laws of the rungs before and the new invariants, in one place. -/
structure Laws (w : World) : Prop where
  band : inBand w.vocabulary w.entities
  slot : oneFactPerSlot w.entities
  one : oneTarget w.vocabulary w.entities
  targets : targetsOk w.vocabulary w.entities
  link : allFacts (linkP w.vocabulary) w.entities
  holders : holdersOk w.vocabulary w.entities
  key : keyId w.entities
  ring : acyc w.entities
  ref : refOk w

theorem rules_key_eq (v : FactVocabulary) (nm : String) :
    FactVocabulary.rules_key v nm = ok ((v.names : names.Names FactRules)[nm]?) := by
  simp [FactVocabulary.rules_key, names.Names.get_key]

theorem counts_hold_true {w : World} (L : Laws w) {k : Nat} {e : Entity}
    (he : (w.entities : Std.ExtTreeMap Nat Entity compare)[k]? = some e) {f : Fact} {r : FactRules}
    (hr : (w.vocabulary.names : names.Names FactRules)[f.name]? = some r) :
    verify.counts_hold w e r f = ok true := by
  have hs := size_lt (hist := w.history) L.ref.2.2.2.1
  unfold verify.counts_hold
  cases r with
  | Solo sh => rfl
  | Linked sh hc tg al =>
    show (do
      let b ← verify.holders_fit w hc f
      if b = true then verify.targets_fit e tg f else ok false) = ok true
    rw [holders_fit_true L.key hs (fun Lm t hL _ => L.holders f.name t sh hc tg al Lm hr hL)]
    simp only [bind_tc_ok, if_true]
    apply targets_fit_true
    intro Lm hL
    by_cases h1 : Lm = 1#u16
    · subst h1
      have hsingle : world.single_target w.vocabulary f.name = ok true := by
        unfold world.single_target fact.Count.is_single
        simp [rules_key_eq, hr, hL, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
          core.cmp.PartialEqU16, liftFun2, core.cmp.impls.PartialEqU16.eq]
      exact L.one k e f.name he hsingle
    · have hone : isOne tg = false := by
        cases tg <;> simp_all [isOne, limitOf]
      exact L.targets k e f.name sh hc tg al Lm he hr hL hone h1

theorem fact_sound_true {w : World} (L : Laws w) {k : Nat} {e : Entity}
    (he : (w.entities : Std.ExtTreeMap Nat Entity compare)[k]? = some e) (i : Usize)
    (hi : i.val < e.facts.val.length) : verify.fact_sound w e i = ok true := by
  have hf : e.facts.val[i.val] ∈ e.facts.val := List.getElem_mem hi
  obtain ⟨r, hr, hnum⟩ := L.band k e _ he hf
  have hnd : (e.facts.deref.val.map slotOf).Nodup := by
    have := L.slot k e he
    simpa [slots, alloc.vec.Vec.deref] using this
  have e1 : verify.slot_before e.facts.deref i = ok false :=
    slot_before_loop_false _ i (by simpa [alloc.vec.Vec.deref] using hi) hnd _ 0#usize rfl
  have e2 := opened_inside_true (L.ref.2.1 k e _ he hf)
  have e3 := value_fits_true hnum
  have hlink := L.link k e _ he hf r hr
  have e4 : verify.link_fits w e r e.facts.val[i.val] = ok true := link_fits_true hlink (fun t ht => by
    obtain ⟨hne, e2, r', he2, hr', hall⟩ := L.ref.1 k e _ t he hf ht
    rw [hr] at hr'
    simp only [Option.some.injEq] at hr'
    subst hr'
    refine ⟨hne, e2, he2, hall ?_⟩
    rw [hlink, ht]; rfl)
  have e5 := counts_hold_true L he hr
  unfold verify.fact_sound
  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hi, rules_key_eq, hr, e1, e2, e3, e4, e5]

theorem up_loop_ok (e : Entity) :
    ∀ (k : Nat) (i : Usize) (r : Option time.EntityId), e.facts.length - i.val = k →
      verify.up_loop e i = ok r →
      r = ((e.facts.val.drop i.val).find? (fun f => locB f.name)).bind (fun f => f.linked_to) := by
  intro k
  induction k with
  | zero =>
    intro i r hn h
    rw [verify.up_loop] at h
    have hge : ¬ i < alloc.vec.Vec.len e.facts := by scalar_tac
    simp only [hge, if_false, ok.injEq] at h
    subst h
    have hle : e.facts.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hle]
  | succ k ih =>
    intro i r hn h
    rw [verify.up_loop] at h
    have hc : i < alloc.vec.Vec.len e.facts := by scalar_tac
    have hlt : i.val < e.facts.val.length := by scalar_tac
    simp [hc, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hlt] at h
    rw [bind_eq_ok] at h
    obtain ⟨str, hstr, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    have hbl := loc_test hstr hb
    subst hbl
    rw [List.drop_eq_getElem_cons hlt, List.find?_cons]
    cases hl : locB e.facts.val[i.val].name
    · simp only [hl, Bool.false_eq_true, if_false] at h ⊢
      rw [bind_eq_ok] at h
      obtain ⟨i2, hi2, h⟩ := h
      obtain ⟨_, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
        (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      rw [hadd] at hi2
      simp only [ok.injEq] at hi2
      subst hi2
      rw [ih _ r (by scalar_tac) h, hval]
      simp
    · simp only [hl, if_true, ok.injEq] at h ⊢
      subst h; rfl

theorem up_eq {w : World} {at' : time.EntityId} {r : Option time.EntityId}
    (h : verify.up w at' = ok r) : r = stepOf w.entities at' := by
  unfold verify.up at h
  simp only [entity_eq, bind_tc_ok] at h
  unfold stepOf
  cases he : (w.entities : Std.ExtTreeMap Nat Entity compare)[at'.val]? with
  | none => simp [he] at h; exact h.symm
  | some e =>
    simp only [he] at h
    have := up_loop_ok e _ 0#usize r rfl h
    simpa [locOf] using this

theorem up_ok (w : World) (at' : time.EntityId) (hs : ∀ e,
    (w.entities : Std.ExtTreeMap Nat Entity compare)[at'.val]? = some e →
      ∃ r, verify.up_loop e 0#usize = ok r) : ∃ r, verify.up w at' = ok r := by
  unfold verify.up
  simp only [entity_eq, bind_tc_ok]
  cases he : (w.entities : Std.ExtTreeMap Nat Entity compare)[at'.val]? with
  | none => exact ⟨none, rfl⟩
  | some e => simpa using hs e he

theorem deref_ok (s : String) :
    ∃ str, alloc.string.String.Insts.CoreOpsDerefDerefStr.deref s = ok str := by
  unfold alloc.string.String.Insts.CoreOpsDerefDerefStr.deref
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem is_loc_ok (str : Str) : ∃ b, fact.is_located_in str = ok b := by
  simp [fact.is_located_in, core.str.Str.as_bytes, core.array.Array.index,
    core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFullSlice, core.slice.index.SliceIndexRangeFullSlice.index,
    slice_eq_u8]

theorem up_loop_total (e : Entity) :
    ∀ (k : Nat) (i : Usize), e.facts.length - i.val = k → ∃ r, verify.up_loop e i = ok r := by
  intro k
  induction k with
  | zero =>
    intro i hn
    rw [verify.up_loop]
    have hge : ¬ i < alloc.vec.Vec.len e.facts := by scalar_tac
    simp [hge]
  | succ k ih =>
    intro i hn
    rw [verify.up_loop]
    have hc : i < alloc.vec.Vec.len e.facts := by scalar_tac
    have hlt : i.val < e.facts.val.length := by scalar_tac
    obtain ⟨str, hstr⟩ := deref_ok e.facts.val[i.val].name
    obtain ⟨b, hb⟩ := is_loc_ok str
    obtain ⟨i2, hadd, _⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    obtain ⟨r, hr⟩ := ih i2 (by scalar_tac)
    cases b <;> simp [hc, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hlt, hstr, hb, hadd, hr]

theorem up_true (w : World) (at' : time.EntityId) : verify.up w at' = ok (stepOf w.entities at') := by
  obtain ⟨r, hr⟩ := up_ok w at' (fun e _ => up_loop_total e _ 0#usize rfl)
  rw [hr, up_eq hr]

/-- INVARIANT 8. The walk up from any entity ends. -/
theorem walk_loop_true {w : World} (hac : acyc w.entities) (start : time.EntityId) (n : Usize)
    (hn : n.val = Std.ExtTreeMap.size (w.entities : Std.ExtTreeMap Nat Entity compare)) :
    ∀ (k : Nat) (at' : time.EntityId) (hops : Usize), n.val - hops.val = k → hops.val ≤ n.val →
      walk w.entities hops.val start = some at' →
      verify.walk_is_finite_loop w n at' hops = ok true := by
  intro k
  induction k with
  | zero =>
    intro at' hops hk hle hw
    rw [verify.walk_is_finite_loop]
    have hge : ¬ hops < n := by scalar_tac
    simp only [hge, if_false, up_true, bind_tc_ok]
    cases hs : stepOf w.entities at' with
    | none => rfl
    | some b =>
      exfalso
      have hw1 : walk w.entities (hops.val + 1) start = some b := by
        simp [walk, hw, hs]
      have := walk_le_size hac hw1
      omega
  | succ k ih =>
    intro at' hops hk hle hw
    rw [verify.walk_is_finite_loop]
    have hc : hops < n := by scalar_tac
    simp only [hc, if_true, up_true, bind_tc_ok]
    cases hs : stepOf w.entities at' with
    | none => rfl
    | some next =>
      obtain ⟨h2, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
        (UScalar.add_spec (x := hops) (y := 1#usize) (by scalar_tac))
      have hval' : h2.val = hops.val + 1 := by simpa using hval
      simp only [hadd, bind_tc_ok]
      apply ih next h2 (by scalar_tac) (by scalar_tac)
      rw [hval']
      simp [walk, hw, hs]

theorem walk_true {w : World} (L : Laws w) (start : time.EntityId) :
    verify.walk_is_finite w start = ok true := by
  have hs := size_lt (hist := w.history) L.ref.2.2.2.1
  obtain ⟨n, hn, hnv⟩ := len_eq w.entities hs
  unfold verify.walk_is_finite world.World.len
  rw [hn]
  simp only [bind_tc_ok]
  exact walk_loop_true L.ring start n hnv _ start 0#usize rfl (by simp) rfl


/-! ## The whole referee -/

theorem entity_loop_true {w : World} (L : Laws w) {k : Nat} {e : Entity}
    (he : (w.entities : Std.ExtTreeMap Nat Entity compare)[k]? = some e) :
    ∀ (n : Nat) (i : Usize), e.facts.length - i.val = n →
      verify.entity_sound_loop w e.id e.entity_type e.name e.existence e.facts i = ok true := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [verify.entity_sound_loop]
    have hge : ¬ i < alloc.vec.Vec.len e.facts := by scalar_tac
    simp only [hge, if_false]
    exact walk_true L e.id
  | succ n ih =>
    intro i hn
    rw [verify.entity_sound_loop]
    have hc : i < alloc.vec.Vec.len e.facts := by scalar_tac
    have hlt : i.val < e.facts.val.length := by scalar_tac
    have hf := fact_sound_true L he i hlt
    obtain ⟨i2, hadd, _⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    simp only [hc, if_true]
    have heta : (⟨e.id, e.entity_type, e.name, e.existence, e.facts⟩ : Entity) = e := rfl
    rw [heta, hf]
    simp only [if_true, hadd, bind_tc_ok]
    exact ih i2 (by scalar_tac)

theorem entity_sound_true {w : World} (L : Laws w) {created : ids.Ids Unit}
    (hcr : ∀ k, k ∈ (w.entities : Std.ExtTreeMap Nat Entity compare) →
      k ∈ (created : Std.ExtTreeMap Nat Unit compare))
    {key : time.EntityId} {e : Entity}
    (he : (w.entities : Std.ExtTreeMap Nat Entity compare)[key.val]? = some e) :
    verify.entity_sound w created key = ok true := by
  have hid : e.id.val = key.val := L.key _ e he
  have hmem : e.id.val ∈ (created : Std.ExtTreeMap Nat Unit compare) := by
    rw [hid]; apply hcr; rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, he]; rfl
  have hcont : Std.ExtTreeMap.contains created e.id.val = true :=
    Std.ExtTreeMap.contains_iff_mem.2 hmem
  have hspan : time.TimeSpan.sound e.existence = ok true := by
    unfold time.TimeSpan.sound
    cases hu : e.existence.until with
    | none => rfl
    | some u =>
      have := (L.ref.2.2.1 key.val e he).2 u hu
      simp only [time.Tick.Insts.CoreCmpPartialOrdTick.ge, ok.injEq, decide_eq_true_eq]
      exact this
  unfold verify.entity_sound
  simp only [entity_eq, he, bind_tc_ok, ids.Ids.contains, hcont, if_true, hspan]
  exact entity_loop_true L he _ 0#usize rfl

theorem all_entities_loop_true {w : World} (L : Laws w) {created : ids.Ids Unit}
    (hcr : ∀ k, k ∈ (w.entities : Std.ExtTreeMap Nat Entity compare) →
      k ∈ (created : Std.ExtTreeMap Nat Unit compare))
    (ids : alloc.vec.Vec time.EntityId)
    (hids : ∀ id ∈ ids.val, ∃ e, (w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]? = some e) :
    ∀ (n : Nat) (k : Usize), ids.length - k.val = n →
      verify.all_entities_sound_loop w created ids k = ok true := by
  intro n
  induction n with
  | zero =>
    intro k hn
    rw [verify.all_entities_sound_loop]
    have hge : ¬ k < alloc.vec.Vec.len ids := by scalar_tac
    simp [hge]
  | succ n ih =>
    intro k hn
    rw [verify.all_entities_sound_loop]
    have hc : k < alloc.vec.Vec.len ids := by scalar_tac
    have hlt : k.val < ids.val.length := by scalar_tac
    obtain ⟨e, he⟩ := hids _ (List.getElem_mem hlt)
    obtain ⟨k2, hadd, _⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := k) (y := 1#usize) (by scalar_tac))
    simp [hc, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hlt, entity_sound_true L hcr he, hadd]
    exact ih k2 (by scalar_tac)

theorem sound_true {w : World} (L : Laws w) : verify.sound w = ok true := by
  have hcr := L.ref.2.2.2.1
  have hs := size_lt (hist := w.history) hcr
  obtain ⟨c', hc', hmem⟩ := created_loop_ok w w.history.deref _ ∅ 0#usize rfl (by
    intro k
    have := hcr k
    simp only [alloc.vec.Vec.deref, Slice.from_val]
    rw [show (0#usize : Usize).val = 0 from rfl, List.drop_zero]
    simp only [Std.ExtTreeMap.not_mem_empty, if_false, Nat.add_zero]
    split at this <;> omega)
  have hcr' : ∀ k, k ∈ (w.entities : Std.ExtTreeMap Nat Entity compare) →
      k ∈ (c' : Std.ExtTreeMap Nat Unit compare) := by
    intro k hk
    rw [hmem]
    right
    have := hcr k
    rw [if_pos hk] at this
    simp only [alloc.vec.Vec.deref, Slice.from_val]
    rw [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, this]
    omega
  obtain ⟨v, hv, _, hids⟩ := ids_eq L.key hs
  unfold verify.sound verify.all_created_once world.World.impl.history event.EventHistory.events
  simp only [ids.Ids.new, bind_tc_ok, hc', if_true]
  unfold verify.all_entities_sound world.World.entity_ids
  simp only [hv, bind_tc_ok]
  exact all_entities_loop_true L hcr' v hids _ 0#usize rfl

theorem verify_true {w : World} (L : Laws w) : verify.verify w = ok true := by
  obtain ⟨_, _, _, hcr, hticks, rows, hfold, hrows⟩ := L.ref
  unfold verify.verify
  rw [refold_eq, hfold]
  simp only [bind_tc_ok]
  rw [same_state_true hrows L.key hcr hticks]
  simp only [bind_tc_ok, if_true]
  exact sound_true L

/-! ## The law -/

/-- THE REFEREE PASSES EVERY WORLD THAT PROPOSALS BUILD. `verify` folds
    the history a second time with its own writer and checks the twelve
    invariants of the spec. In every world that proposals build from an
    empty world, it answers `true`. The vocabulary must declare
    `located_in` with one target, as the crate does. -/
theorem every_proposed_world_verifies (v : FactVocabulary) (w0 w : World)
    (h0 : World.new v = ok w0) (hv : world.single_target v "located_in" = ok true)
    (hr : ReachP w0 w) : verify.verify w = ok true := by
  have hvoc : w.vocabulary = v := by
    rw [reachP_vocab hr]
    simp only [World.new, ids.Ids.new, EventHistory.new, bind_tc_ok, ok.injEq] at h0
    rw [← h0]
  have ht := every_proposed_world_targets v w0 w h0 hr
  apply verify_true
  exact {
    band := every_proposed_world_in_band v w0 w h0 hr
    slot := every_world_one_fact_per_slot v w0 w h0 (reachP_reach hr)
    one := every_world_one_target v w0 w h0 (reachP_reach hr)
    targets := ht.1
    link := ht.2
    holders := every_proposed_world_holders v w0 w h0 hr
    key := by
      apply (reachP_holders hr _).2
      simp only [World.new, ids.Ids.new, EventHistory.new, bind_tc_ok, ok.injEq] at h0
      subst h0
      exact ⟨fun n t _ _ _ _ _ _ _ => by simp [holdersCount, Std.ExtTreeMap.keys_eq_nil_iff.2 rfl],
        fun k _ hk => by simp at hk⟩
    ring := every_proposed_world_acyclic v w0 w h0 hv hr
    ref := reachP_ref v w0 w h0 hr }

end hourglass
