-- The rung 5 count laws: a name never has more targets, or more
-- holders, than its count allows, in every world that proposals build.
import Hourglass.Direction

open Aeneas Aeneas.Std Result

namespace hourglass

open world event fact entity

/-! ## The other targets of an entity -/

/-- The target of a fact, when it names `nm` and a target other than `t`. -/
def otherT (nm : String) (t : time.EntityId) (f : Fact) : Option time.EntityId :=
  if f.name = nm then
    match f.linked_to with
    | some x => if x ≠ t then some x else none
    | none => none
  else none

theorem push_other_target_ok {out r : alloc.vec.Vec time.EntityId} {f : Fact} {nm : String}
    {t : time.EntityId} (h : validate.push_other_target out f nm t = ok r) :
    r.val = out.val ++ (otherT nm t f).toList := by
  unfold validate.push_other_target at h
  unfold otherT
  simp only [alloc.string.String.Insts.CoreCmpPartialEqString.eq, bind_tc_ok] at h
  by_cases hn : f.name = nm
  · simp only [hn, decide_true, if_true] at h ⊢
    cases hl : f.linked_to with
    | none => simp only [hl] at h; simp only [ok.injEq] at h; subst h; simp
    | some x =>
      simp only [hl, time.EntityId.Insts.CoreCmpPartialEqEntityId.ne, bind_tc_ok] at h
      by_cases hx : x ≠ t
      · simp [hx] at h ⊢
        rw [push_val_any h]
      · simp only [hx, decide_false, Bool.false_eq_true, if_false, ok.injEq] at h ⊢
        subst h; simp
  · simp only [hn, decide_false, Bool.false_eq_true, if_false, ok.injEq] at h ⊢
    subst h; simp

theorem targets_except_loop_ok (nm : String) (t : time.EntityId) (row : Entity) :
    ∀ (n : Nat) (out r : alloc.vec.Vec time.EntityId) (i : Usize),
      row.facts.length - i.val = n →
      validate.targets_except_loop nm t out row i = ok r →
      r.val = out.val ++ (row.facts.val.drop i.val).filterMap (otherT nm t) := by
  intro n
  induction n with
  | zero =>
    intro out r i hn h
    rw [validate.targets_except_loop] at h
    have hge : ¬ i < alloc.vec.Vec.len row.facts := by scalar_tac
    simp only [hge, if_false, ok.injEq] at h
    subst h
    have hle : row.facts.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hle]
  | succ n ih =>
    intro out r i hn h
    rw [validate.targets_except_loop] at h
    have hc : i < alloc.vec.Vec.len row.facts := by scalar_tac
    have hlt : i.val < row.facts.val.length := by scalar_tac
    simp [hc, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hlt] at h
    rw [bind_eq_ok] at h
    obtain ⟨out1, h1, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨i2, hi2, h⟩ := h
    obtain ⟨_, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [hadd] at hi2
    simp only [ok.injEq] at hi2
    subst hi2
    rw [ih out1 r _ (by scalar_tac) h, push_other_target_ok h1,
      List.drop_eq_getElem_cons hlt, List.filterMap_cons, hval]
    cases otherT nm t row.facts.val[i.val] <;> simp

theorem targets_except_ok {w : World} {who : time.EntityId} {nm : String} {t : time.EntityId}
    {r : alloc.vec.Vec time.EntityId} (h : validate.targets_except w who nm t = ok r) :
    ∀ e, (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? = some e →
      r.val = e.facts.val.filterMap (otherT nm t) := by
  intro e he
  unfold validate.targets_except at h
  simp only [entity_eq, he, bind_tc_ok] at h
  simpa using targets_except_loop_ok nm t e _ _ r 0#usize rfl h

/-! ## The count check of the gate -/

def limitOf : Count → Option Std.U16
  | .One => some 1#u16
  | .Many => none
  | .AtMost n => some n

@[simp] theorem limit_eq (c : Count) : c.limit = ok (limitOf c) := by
  cases c <;> simp [Count.limit, limitOf]

def isOne : Count → Bool
  | .One => true
  | _ => false

@[simp] theorem count_eq_one (c : Count) :
    Count.Insts.CoreCmpPartialEqCount.eq c .One = ok (isOne c) := by
  cases c <;> simp [Count.Insts.CoreCmpPartialEqCount.eq, isOne, fact.Count.read_discriminant]

/-- A CLEAN COUNT CHECK ON THE TARGET SIDE. When the limit is above one,
    the other targets and the new one fit the limit. -/
theorem counts_targets_clean {w : World} {who : time.EntityId} {nm : String} {r : FactRules}
    {t : time.EntityId} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.counts_fit w who nm r t o = ok o') (he : o'.val = [])
    {sh : Shape} {hc tg : Count} {al : alloc.collections.btree.map.BTreeMap entity.EntityType
      (alloc.vec.Vec entity.EntityType) Global}
    (hr : r = .Linked sh hc tg al) {L : Std.U16} (hL : limitOf tg = some L)
    (hone : isOne tg = false) (hL1 : L ≠ 1#u16) :
    ∃ pa, validate.targets_except w who nm t = ok pa ∧ pa.val.length < L.val := by
  subst hr
  unfold validate.counts_fit at h
  simp only [limit_eq, bind_tc_ok] at h
  rw [bind_eq_ok] at h
  obtain ⟨out1, h1, h⟩ := h
  have hr1 : out1.val <+: out1.val := List.prefix_refl _
  have p1 : out1.val <+: o'.val := grows_of (by grows) h
  have e1 := nil_of_prefix_nil p1 he
  simp [hL, hone, hL1, lift] at h
  rw [bind_eq_ok] at h
  obtain ⟨pa, hpa, h⟩ := h
  refine ⟨pa, hpa, ?_⟩
  split at h
  · rw [bind_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    exact absurd he (push_ne h)
  · rename_i hlt
    omega

/-- Does the name take a target? -/
def takesT : FactRules → Bool
  | .Solo _ => false
  | .Linked .. => true

@[simp] theorem takes_target_eq (r : FactRules) : r.takes_target = ok (takesT r) := by
  cases r <;> simp [FactRules.takes_target, takesT]

theorem target_fits_clean {nm : String} {r : FactRules} {lt : Option time.EntityId}
    {o o' : alloc.vec.Vec reject.Rejection} (h : validate.target_fits nm r lt o = ok o')
    (he : o'.val = []) : takesT r = lt.isSome := by
  unfold validate.target_fits at h
  simp only [takes_target_eq, alloc.string.String.Insts.CoreCloneClone.clone, bind_tc_ok] at h
  cases r <;> cases lt <;> simp [takesT] at h ⊢ <;> exact absurd he (push_ne h)

/-- A START WITH NO FAULT gives its name a target exactly when the name
    takes one, and it fits the limit of targets. -/
theorem start_count_clean {w : World} {who : time.EntityId} {nm : String} {v : Option Std.I64}
    {lt : Option time.EntityId} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.start w who nm v lt o = ok o') (he : o'.val = [])
    (r : FactRules) (hr : (w.vocabulary.names : names.Names FactRules)[nm]? = some r) :
    takesT r = lt.isSome ∧
    (∀ t, lt = some t → ∀ sh hc tg al, r = .Linked sh hc tg al → ∀ L, limitOf tg = some L →
      isOne tg = false → L ≠ 1#u16 →
      ∃ pa, validate.targets_except w who nm t = ok pa ∧ pa.val.length < L.val) := by
  unfold validate.start at h
  rw [bind_eq_ok] at h
  obtain ⟨⟨holder, out1⟩, h1, h⟩ := h
  simp only [FactVocabulary.rules_key, names.Names.get_key] at h
  simp [hr] at h
  rw [bind_eq_ok] at h
  obtain ⟨out2, h2, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out3, h3, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out4, h4, h⟩ := h
  have hr3 : out3.val <+: out3.val := List.prefix_refl _
  have p4 : out3.val <+: out4.val := grows_of (by grows) h4
  have hr4 : out4.val <+: out4.val := List.prefix_refl _
  have p5 : out4.val <+: o'.val := grows_of (by grows) h
  have e4 := nil_of_prefix_nil p5 he
  have e3 := nil_of_prefix_nil p4 e4
  refine ⟨target_fits_clean h3 e3, ?_⟩
  intro t ht sh hc tg al hrl L hL hone hL1
  subst ht hrl
  simp only [takesT, if_true] at h4
  rw [bind_eq_ok] at h4
  obtain ⟨_, _, h4⟩ := h4
  rw [bind_eq_ok] at h4
  obtain ⟨out5, h5, h4⟩ := h4
  rw [bind_eq_ok] at h4
  obtain ⟨out6, h6, h4⟩ := h4
  have hr6 : out6.val <+: out6.val := List.prefix_refl _
  have p6 : out6.val <+: out4.val := grows_of (by grows) h4
  have e6 := nil_of_prefix_nil p6 e4
  rw [bind_eq_ok] at h6
  obtain ⟨_, _, h6⟩ := h6
  rw [bind_eq_ok] at h6
  obtain ⟨out7, _, h6⟩ := h6
  exact counts_targets_clean h6 e6 rfl hL hone hL1

/-! ## A fact property that reads only the slot -/

/-- Every fact of every entity has the property `P`. -/
def allFacts (P : Fact → Prop) (m : ids.Ids Entity) : Prop :=
  ∀ (k : Nat) (e : Entity) (x : Fact), (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e →
    x ∈ e.facts.val → P x

theorem af_erase {P : Fact → Prop} {m : ids.Ids Entity} (h : allFacts P m) (k : Nat) :
    allFacts P (Std.ExtTreeMap.erase m k) := by
  intro j e x hj hx
  rw [Std.ExtTreeMap.getElem?_erase] at hj
  split at hj
  · simp at hj
  · exact h j e x hj hx

theorem af_insert {P : Fact → Prop} {m : ids.Ids Entity} (h : allFacts P m) (k : Nat)
    (row : Entity) (hr : ∀ x ∈ row.facts.val, P x) : allFacts P (Std.ExtTreeMap.insert m k row) := by
  intro j e x hj hx
  rw [Std.ExtTreeMap.getElem?_insert] at hj
  split at hj
  · simp only [Option.some.injEq] at hj; subst hj; exact hr x hx
  · exact h j e x hj hx

/-- APPLY KEEPS A PROPERTY OF THE SLOT. If every fact has a property
    that reads only its name and its target, and the new fact of a start
    has it too, then every fact has it after `apply`. -/
theorem apply_all_facts (P : Fact → Prop) (hP : ∀ x y, slotOf x = slotOf y → P x → P y)
    (m : ids.Ids Entity) (v : FactVocabulary) (ev : Event) (m' : ids.Ids Entity)
    (h : allFacts P m)
    (hnew : ∀ who nm value lt, ev.kind = .FactStart who nm value lt →
      P { «name» := nm, value := value, linked_to := lt, opened := ev.id })
    (ha : World.apply m v ev = ok m') : allFacts P m' := by
  unfold World.apply at ha
  cases hk : ev.kind <;> simp only [hk] at ha
  case EntityCreated id ty nm =>
    simp only [ids.Ids.contains, bind_tc_ok] at ha
    split at ha
    · simp only [ok.injEq] at ha; subst ha; exact h
    · simp only [alloc.string.String.Insts.CoreCloneClone.clone, time.TimeSpan.open,
        ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
      subst ha
      exact af_insert h _ _ (fun x hx => by simp [alloc.vec.Vec.new] at hx)
  case EntityDestroyed id =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[id.val]? with
    | none => simp [hr] at ha; subst ha; exact af_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      split at ha
      all_goals
        simp only [bind_tc_ok, ok.injEq] at ha
        subst ha
        exact af_insert (af_erase h _) _ _ (fun x hx => h _ _ x hr hx)
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨wide, _, ha⟩ := ha
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact af_erase h _
    | some row =>
      simp [hr, ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨v1, hv1, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply af_insert (af_erase h _)
      intro x hx
      rw [push_val_any hv1, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · have hsub : x ∈ row.facts.val := by
          cases wide
          · simp only [Bool.false_eq_true, if_false, world.drop_slot] at hvf
            rw [drop_slot_ok hvf, List.mem_filter] at hx; exact hx.1
          · simp only [if_true, world.drop_name] at hvf
            rw [drop_name_ok hvf, List.mem_filter] at hx; exact hx.1
        exact h _ _ x hr hsub
      · exact hnew who nm value lt hk
  case FactUpdate who nm lt fr tv =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact af_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨o1, ho1, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply af_insert (af_erase h _)
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
        have hi : i.val < row.facts.val.length := by
          simpa [alloc.vec.Vec.deref] using (hlt.1 i rfl).1
        simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize] at hvf
        simp [hi] at hvf
        subst hvf
        intro x hx
        simp only [alloc.vec.Vec.set_val_eq, List.set_set] at hx
        rcases List.mem_or_eq_of_mem_set hx with hx | hx
        · exact h _ _ x hr hx
        · rw [hx]
          exact hP _ _ (by simp [slotOf]) (h _ _ _ hr (List.getElem_mem hi))
  case FactEnd who nm lt =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact af_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply af_insert (af_erase h _)
      intro x hx
      rw [drop_slot_ok hvf, List.mem_filter] at hx
      exact h _ _ x hr hx.1

/-! ## The targets law -/

/-- A name with a limit of targets above one is not single-target. -/
theorem single_target_false {v : FactVocabulary} {nm : String} {sh : Shape} {hc tg : Count}
    {al : alloc.collections.btree.map.BTreeMap entity.EntityType (alloc.vec.Vec entity.EntityType) Global}
    (hr : (v.names : names.Names FactRules)[nm]? = some (.Linked sh hc tg al))
    {L : Std.U16} (hL : limitOf tg = some L) (hL1 : L ≠ 1#u16) :
    world.single_target v nm = ok false := by
  unfold world.single_target
  simp [FactVocabulary.rules_key, names.Names.get_key, hr, Count.is_single, hL,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq]
  intro h; exact hL1 (by scalar_tac)

/-- The facts of a name, other than the slot of one target, are the
    other targets, when every fact of the name has a target. -/
theorem count_other (facts : List Fact) (nm : String) (t : time.EntityId)
    (hsome : ∀ f ∈ facts, f.name = nm → f.linked_to.isSome) :
    (facts.filter (fun f => !inSlot f nm (some t))).countP (fun f => decide (f.name = nm)) =
      (facts.filterMap (otherT nm t)).length := by
  induction facts with
  | nil => simp
  | cons f rest ih =>
    have ih' := ih (fun g hg => hsome g (List.mem_cons_of_mem _ hg))
    by_cases hn : f.name = nm
    · have hs := hsome f (List.mem_cons_self) hn
      cases hl : f.linked_to with
      | none => simp [hl] at hs
      | some x =>
        have hin : inSlot f nm (some t) = decide (x = t) := by simp [inSlot, slotOf, hn, hl]
        have ho : otherT nm t f = if x ≠ t then some x else none := by simp [otherT, hn, hl]
        rw [List.filter_cons, List.filterMap_cons, hin, ho]
        by_cases hx : x = t
        · simp only [hx, decide_true, Bool.not_true, Bool.false_eq_true, if_false, ne_eq,
            not_true_eq_false]
          exact ih'
        · simp only [hx, decide_false, Bool.not_false, if_true, ne_eq, not_false_eq_true,
            List.countP_cons, List.length_cons, hn, decide_true]
          rw [ih']
    · have hin : inSlot f nm (some t) = false := by simp [inSlot, slotOf, hn]
      have ho : otherT nm t f = none := by simp [otherT, hn]
      rw [List.filter_cons, List.filterMap_cons, hin, ho]
      simp only [Bool.not_false, if_true, List.countP_cons, hn, decide_false,
        Bool.false_eq_true, if_false, Nat.add_zero]
      exact ih'

/-- A fact carries a target exactly when its name takes one. -/
def linkP (v : FactVocabulary) (x : Fact) : Prop :=
  ∀ r, (v.names : names.Names FactRules)[x.name]? = some r → takesT r = x.linked_to.isSome

/-- What a clean gate says about the counts of a start. -/
def countClean (w : World) : EventKind → Prop
  | .FactStart who nm _ lt =>
    ∀ r, (w.vocabulary.names : names.Names FactRules)[nm]? = some r →
      takesT r = lt.isSome ∧
      (∀ t, lt = some t → ∀ sh hc tg al, r = .Linked sh hc tg al → ∀ L, limitOf tg = some L →
        isOne tg = false → L ≠ 1#u16 →
        ∃ pa, validate.targets_except w who nm t = ok pa ∧ pa.val.length < L.val)
  | _ => True

theorem validate_count {w : World} {t : time.Tick} {k : EventKind}
    {f : alloc.vec.Vec reject.Rejection}
    (h : validate.validate w t k = ok f) (he : f.val = []) : countClean w k := by
  unfold validate.validate at h
  rw [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out, _, h⟩ := h
  cases k with
  | FactStart who nm value lt => exact fun r hr => start_count_clean h he r hr
  | _ => trivial

/-- A name with a limit of targets above one holds at most that many
    facts on each entity. -/
def targetsOk (v : FactVocabulary) (m : ids.Ids Entity) : Prop :=
  ∀ (k : Nat) (e : Entity) (n : String) (sh : Shape) (hc tg : Count)
    (al : alloc.collections.btree.map.BTreeMap entity.EntityType (alloc.vec.Vec entity.EntityType) Global)
    (L : Std.U16), (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e →
    (v.names : names.Names FactRules)[n]? = some (.Linked sh hc tg al) →
    limitOf tg = some L → isOne tg = false → L ≠ 1#u16 → countName e n ≤ L.val

theorem tk_erase {v : FactVocabulary} {m : ids.Ids Entity} (h : targetsOk v m) (k : Nat) :
    targetsOk v (Std.ExtTreeMap.erase m k) := by
  intro j e n sh hc tg al L hj
  rw [Std.ExtTreeMap.getElem?_erase] at hj
  split at hj
  · simp at hj
  · exact h j e n sh hc tg al L hj

theorem tk_insert {v : FactVocabulary} {m : ids.Ids Entity} (h : targetsOk v m) (k : Nat)
    (row : Entity) (hr : ∀ n sh hc tg al L,
      (v.names : names.Names FactRules)[n]? = some (.Linked sh hc tg al) →
      limitOf tg = some L → isOne tg = false → L ≠ 1#u16 → countName row n ≤ L.val) :
    targetsOk v (Std.ExtTreeMap.insert m k row) := by
  intro j e n sh hc tg al L hj
  rw [Std.ExtTreeMap.getElem?_insert] at hj
  split at hj
  · simp only [Option.some.injEq] at hj; subst hj; exact hr n sh hc tg al L
  · exact h j e n sh hc tg al L hj

/-- APPLY KEEPS THE LIMIT OF TARGETS, for an event with a clean count. -/
theorem apply_targets (w : World) (ev : Event) (m' : ids.Ids Entity)
    (h : targetsOk w.vocabulary w.entities) (hl : allFacts (linkP w.vocabulary) w.entities)
    (hc : countClean w ev.kind) (ha : World.apply w.entities w.vocabulary ev = ok m') :
    targetsOk w.vocabulary m' := by
  unfold World.apply at ha
  cases hk : ev.kind <;> simp only [hk] at ha <;> rw [hk] at hc
  case EntityCreated id ty nm =>
    simp only [ids.Ids.contains, bind_tc_ok] at ha
    split at ha
    · simp only [ok.injEq] at ha; subst ha; exact h
    · simp only [alloc.string.String.Insts.CoreCloneClone.clone, time.TimeSpan.open,
        ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
      subst ha
      exact tk_insert h _ _ (fun n _ _ _ _ _ _ _ _ _ => by simp [countName, alloc.vec.Vec.new])
  case EntityDestroyed id =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]? with
    | none => simp [hr] at ha; subst ha; exact tk_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      split at ha
      all_goals
        simp only [bind_tc_ok, ok.injEq] at ha
        subst ha
        exact tk_insert (tk_erase h _) _ _ (fun n sh hc tg al L hn hL hone hL1 => by
          simpa [countName] using h _ _ n sh hc tg al L hr hn hL hone hL1)
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨wide, hwide, ha⟩ := ha
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact tk_erase h _
    | some row =>
      simp [hr, ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨v1, hv1, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply tk_insert (tk_erase h _)
      intro n sh hcn tg al L hn hL hone hL1
      simp only [countName, push_val_any hv1, List.countP_append]
      by_cases hnm : nm = n
      · -- The name of the event: the new fact takes one place, and the
        -- other targets fill the rest.
        subst hnm
        obtain ⟨hlink, hbound⟩ := hc _ hn
        simp only [takesT] at hlink
        cases lt with
        | none => simp at hlink
        | some t =>
          obtain ⟨pa, hpa, hlt⟩ := hbound t rfl sh hcn tg al rfl L hL hone hL1
          rw [single_target_false hn hL hL1] at hwide
          simp only [ok.injEq] at hwide
          subst hwide
          simp only [Bool.false_eq_true, if_false, world.drop_slot] at hvf
          rw [drop_slot_ok hvf]
          have hsome : ∀ f ∈ row.facts.val, f.name = nm → f.linked_to.isSome := by
            intro f hf hfn
            have := hl _ _ f hr hf _ (by rw [hfn]; exact hn)
            simpa [takesT] using this.symm
          rw [count_other _ nm t hsome, ← targets_except_ok hpa row hr]
          simp
          omega
      · -- Another name: the new fact does not count, and the drop only
        -- takes facts away.
        have hold := h _ _ n sh hcn tg al L hr hn hL hone hL1
        have hnew : List.countP (fun f : Fact => decide (f.name = n))
            [({ «name» := nm, value := value, linked_to := lt, opened := ev.id } : Fact)] = 0 := by
          simp [hnm]
        rw [hnew, Nat.add_zero]
        refine le_trans ?_ hold
        cases wide
        · simp only [Bool.false_eq_true, if_false, world.drop_slot] at hvf
          rw [drop_slot_ok hvf]; exact countP_filter_le _ _ _
        · simp only [if_true, world.drop_name] at hvf
          rw [drop_name_ok hvf]; exact countP_filter_le _ _ _
  case FactUpdate who nm lt fr tv =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact tk_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨o1, ho1, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply tk_insert (tk_erase h _)
      intro n sh hcn tg al L hn hL hone hL1
      have hnames : vf.val.map (fun f : Fact => f.name) = row.facts.val.map (fun f : Fact => f.name) := by
        cases o1 with
        | none => simp only [ok.injEq] at hvf; subst hvf; rfl
        | some i =>
          obtain ⟨_, ho1', hlt⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
            (slot_index_spec row.facts.deref nm lt)
          rw [ho1] at ho1'
          simp only [ok.injEq] at ho1'
          subst ho1'
          have hi : i.val < row.facts.val.length := by
            simpa [alloc.vec.Vec.deref] using (hlt.1 i rfl).1
          simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize] at hvf
          simp [hi] at hvf
          subst hvf
          simp [List.map_set]
          have : (row.facts.val)[i.val].name =
              (row.facts.val.map (fun f : Fact => f.name))[i.val]'(by simpa using hi) := by simp
          rw [this, List.set_getElem_self]
      have hcnt : countName { row with facts := vf } n = countName row n := by
        simp only [countName]
        have := congrArg (List.countP (fun s : String => decide (s = n))) hnames
        simpa [List.countP_map, Function.comp_def] using this
      simpa [hcnt] using h _ _ n sh hcn tg al L hr hn hL hone hL1
  case FactEnd who nm lt =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact tk_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply tk_insert (tk_erase h _)
      intro n sh hcn tg al L hn hL hone hL1
      simp only [countName, drop_slot_ok hvf]
      exact le_trans (countP_filter_le _ _ _) (h _ _ n sh hcn tg al L hr hn hL hone hL1)

/-! ## Every world that proposals build -/

theorem reachP_targets {w u : World} (hr : ReachP w u)
    (h : targetsOk w.vocabulary w.entities ∧ allFacts (linkP w.vocabulary) w.entities) :
    targetsOk u.vocabulary u.entities ∧ allFacts (linkP u.vocabulary) u.entities := by
  induction hr with
  | refl => exact h
  | @step u1 u2 t k r _ hp ih =>
    cases r with
    | Err f => rw [(propose_err u1 u2 t k f hp).1]; exact ih
    | Ok id =>
      obtain ⟨⟨f, hv, he⟩, hc⟩ := propose_ok u1 u2 t k id hp
      obtain ⟨_, _, hvoc⟩ := commit_ok hc
      have hcount := validate_count hv he
      rw [hvoc]
      refine ⟨apply_targets u1 ⟨id, t, k⟩ _ ih.1 ih.2 hcount (commit_apply hc), ?_⟩
      apply apply_all_facts (linkP u1.vocabulary) _ _ _ ⟨id, t, k⟩ _ ih.2 _ (commit_apply hc)
      · intro x y hxy hx r hr
        have hn : x.name = y.name := congrArg Prod.fst hxy
        have hl : x.linked_to = y.linked_to := congrArg Prod.snd hxy
        rw [← hl]
        exact hx r (by rw [hn]; exact hr)
      · intro who nm value lt hk r hr
        rw [show (⟨id, t, k⟩ : Event).kind = k from rfl] at hk
        subst hk
        exact (hcount r hr).1

/-- A NAME NEVER HAS MORE TARGETS THAN ITS COUNT ALLOWS. In every world
    that proposals build from an empty world, a name with a limit of
    targets above one holds at most that many facts on each entity, and
    a fact carries a target exactly when its name takes one. -/
theorem every_proposed_world_targets (v : FactVocabulary) (w0 w : World)
    (h0 : World.new v = ok w0) (hr : ReachP w0 w) :
    targetsOk w.vocabulary w.entities ∧ allFacts (linkP w.vocabulary) w.entities := by
  apply reachP_targets hr
  simp only [World.new, ids.Ids.new, EventHistory.new, bind_tc_ok, ok.injEq] at h0
  subst h0
  exact ⟨fun k _ _ _ _ _ _ _ hk => by simp at hk, fun k _ _ hk => by simp at hk⟩

/-! ## The holders of a name about a target -/

/-- Does the entity hold the name about the target? -/
def holdsB (n : String) (t : time.EntityId) (e : Entity) : Bool :=
  e.facts.val.any (fun f => inSlot f n (some t))

/-- One step of `holders_except`, as a pure function. -/
def pushH (m : ids.Ids Entity) (n : String) (t who : time.EntityId) (id : time.EntityId) :
    Option time.EntityId :=
  match (m : Std.ExtTreeMap Nat Entity compare)[id.val]? with
  | some row => if row.id ≠ who ∧ holdsB n t row = true then some row.id else none
  | none => none

theorem slot_index_is_some (facts : alloc.vec.Vec Fact) (n : String) (l : Option time.EntityId)
    (o : Option Usize) (ho : world.slot_index facts.deref n l = ok o) :
    o.isSome = facts.val.any (fun f => inSlot f n l) := by
  obtain ⟨o', ho', post⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1 (slot_index_spec facts.deref n l)
  rw [ho] at ho'
  simp only [ok.injEq] at ho'
  subst ho'
  cases o with
  | none =>
    have := post.2 rfl
    simp only [Option.isSome_none, Bool.false_eq, List.any_eq_false]
    intro f hf
    simpa using this f (by simpa [alloc.vec.Vec.deref] using hf)
  | some i =>
    obtain ⟨hj, hin⟩ := post.1 i rfl
    rw [Option.isSome_some, eq_comm, List.any_eq_true]
    exact ⟨_, List.getElem_mem (by simpa [alloc.vec.Vec.deref] using hj),
      by simpa [alloc.vec.Vec.deref] using hin⟩

theorem push_holder_ok {out r : alloc.vec.Vec time.EntityId} {w : World} {id : time.EntityId}
    {n : String} {t who : time.EntityId}
    (h : validate.push_holder out w id n t who = ok r) :
    r.val = out.val ++ (pushH w.entities n t who id).toList := by
  unfold validate.push_holder at h
  unfold pushH
  simp only [entity_eq, bind_tc_ok] at h
  cases he : (w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]? with
  | none => simp only [he, ok.injEq] at h; subst h; simp
  | some row =>
    rw [he] at h
    simp only [time.EntityId.Insts.CoreCmpPartialEqEntityId.ne, bind_tc_ok] at h
    by_cases hw : row.id ≠ who
    · simp [hw] at h
      rw [bind_eq_ok] at h
      obtain ⟨o1, ho1, h⟩ := h
      have hs := slot_index_is_some row.facts n (some t) o1 ho1
      by_cases hh : holdsB n t row = true
      · have : o1.isSome = true := by rw [hs]; exact hh
        simp [this] at h
        rw [push_val_any h]
        simp [hw, hh]
      · have : o1.isSome = false := by rw [hs]; simpa [holdsB] using hh
        simp [this] at h
        subst h
        simp [hh]
    · simp [hw] at h
      subst h
      simp [hw]

theorem holders_except_loop_ok (w : World) (n : String) (t who : time.EntityId)
    (ids : alloc.vec.Vec time.EntityId) :
    ∀ (k : Nat) (out r : alloc.vec.Vec time.EntityId) (i : Usize), ids.length - i.val = k →
      validate.holders_except_loop w n t who ids out i = ok r →
      r.val = out.val ++ (ids.val.drop i.val).filterMap (pushH w.entities n t who) := by
  intro k
  induction k with
  | zero =>
    intro out r i hn h
    rw [validate.holders_except_loop] at h
    have hge : ¬ i < alloc.vec.Vec.len ids := by scalar_tac
    simp only [hge, if_false, ok.injEq] at h
    subst h
    have hle : ids.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hle]
  | succ k ih =>
    intro out r i hn h
    rw [validate.holders_except_loop] at h
    have hc : i < alloc.vec.Vec.len ids := by scalar_tac
    have hlt : i.val < ids.val.length := by scalar_tac
    simp [hc, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hlt] at h
    rw [bind_eq_ok] at h
    obtain ⟨out1, h1, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨i2, hi2, h⟩ := h
    obtain ⟨_, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [hadd] at hi2
    simp only [ok.injEq] at hi2
    subst hi2
    rw [ih out1 r _ (by scalar_tac) h, push_holder_ok h1,
      List.drop_eq_getElem_cons hlt, List.filterMap_cons, hval]
    cases pushH w.entities n t who ids.val[i.val] <;> simp

/-- The ids of the model, as `u32` values. -/
def idsOf (m : ids.Ids Entity) : List time.EntityId :=
  (Std.ExtTreeMap.keys m).filterMap (fun k =>
    if h : k < 2 ^ UScalarTy.U32.numBits then some (UScalar.ofNatCore k h) else none)

theorem holders_except_ok {w : World} {n : String} {t who : time.EntityId}
    {r : alloc.vec.Vec time.EntityId} (h : validate.holders_except w n t who = ok r) :
    r.val = (idsOf w.entities).filterMap (pushH w.entities n t who) := by
  unfold validate.holders_except world.World.entity_ids ids.Ids.ids at h
  rw [bind_eq_ok] at h
  obtain ⟨ids, hids, h⟩ := h
  dsimp only at hids
  split at hids
  · simp only [ok.injEq] at hids
    subst hids
    have := holders_except_loop_ok w n t who _ _ _ r 0#usize rfl h
    simpa [idsOf] using this
  · simp at hids

/-! ## Counting holders over the keys -/

/-- Does the entity at key `k` hold the name about the target? -/
def holdsAt (m : ids.Ids Entity) (n : String) (t : time.EntityId) (k : Nat) : Bool :=
  match (m : Std.ExtTreeMap Nat Entity compare)[k]? with
  | some e => holdsB n t e
  | none => false

/-- The number of entities that hold the name about the target. -/
def holdersCount (m : ids.Ids Entity) (n : String) (t : time.EntityId) : Nat :=
  (Std.ExtTreeMap.keys m).countP (holdsAt m n t)

/-- The key of each entity is its own id. -/
def keyId (m : ids.Ids Entity) : Prop :=
  ∀ (k : Nat) (e : Entity), (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e → e.id.val = k

theorem countP_split (l : List Nat) (hn : l.Nodup) (w : Nat) (hw : w ∈ l) (a : Bool)
    (p : Nat → Bool) :
    l.countP (fun k => if k = w then a else p k) =
      l.countP (fun k => decide (k ≠ w) && p k) + (if a then 1 else 0) := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hw
  have hn' := hn
  rw [List.nodup_append] at hn'
  obtain ⟨hn1, hn2, hdis⟩ := hn'
  have h1 : w ∉ l1 := fun h => hdis w h w (List.mem_cons_self) rfl
  have h2 : w ∉ l2 := (List.nodup_cons.1 hn2).1
  have e1 : l1.countP (fun k => if k = w then a else p k) =
      l1.countP (fun k => decide (k ≠ w) && p k) :=
    List.countP_congr (fun k hk => by
      have : k ≠ w := fun h => h1 (h ▸ hk)
      simp [this])
  have e2 : l2.countP (fun k => if k = w then a else p k) =
      l2.countP (fun k => decide (k ≠ w) && p k) :=
    List.countP_congr (fun k hk => by
      have : k ≠ w := fun h => h2 (h ▸ hk)
      simp [this])
  simp only [List.countP_append, List.countP_cons, e1, e2]
  cases a <;> simp
  omega

theorem keys_perm_replace (m : ids.Ids Entity) (k : Nat) (hk : k ∈ (m : Std.ExtTreeMap Nat Entity compare))
    (row : Entity) :
    (Std.ExtTreeMap.keys (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k row)).Perm
      (Std.ExtTreeMap.keys m) := by
  rw [List.perm_ext_iff_of_nodup Std.ExtTreeMap.nodup_keys Std.ExtTreeMap.nodup_keys]
  intro j
  simp only [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_insert, Std.ExtTreeMap.mem_erase]
  by_cases hj : k = j
  · subst hj; simp [hk]
  · simp [hj]

/-- REPLACE ONE ENTITY. The count changes only at that key. -/
theorem count_replace (m : ids.Ids Entity) (k : Nat) (row : Entity)
    (hk : k ∈ (m : Std.ExtTreeMap Nat Entity compare)) (n : String) (t : time.EntityId) :
    holdersCount (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k row) n t =
      (Std.ExtTreeMap.keys m).countP (fun j => decide (j ≠ k) && holdsAt m n t j) +
      (if holdsB n t row then 1 else 0) := by
  unfold holdersCount
  rw [(keys_perm_replace m k hk row).countP_eq]
  have : ∀ j, holdsAt (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k row) n t j =
      (if j = k then holdsB n t row else holdsAt m n t j) := by
    intro j
    unfold holdsAt
    rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase]
    by_cases hj : j = k
    · subst hj; simp
    · simp [Ne.symm hj, hj]
  conv => lhs; rw [List.countP_congr (fun j _ => by rw [this j])]
  exact countP_split _ Std.ExtTreeMap.nodup_keys k (Std.ExtTreeMap.mem_keys.2 hk) _ _

theorem count_before (m : ids.Ids Entity) (k : Nat) (row : Entity)
    (hr : (m : Std.ExtTreeMap Nat Entity compare)[k]? = some row) (n : String) (t : time.EntityId) :
    holdersCount m n t =
      (Std.ExtTreeMap.keys m).countP (fun j => decide (j ≠ k) && holdsAt m n t j) +
      (if holdsB n t row then 1 else 0) := by
  unfold holdersCount
  have hk : k ∈ (m : Std.ExtTreeMap Nat Entity compare) := by
    rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hr]; rfl
  have : ∀ j, holdsAt m n t j = (if j = k then holdsB n t row else holdsAt m n t j) := by
    intro j
    by_cases hj : j = k
    · subst hj; simp [holdsAt, hr]
    · simp [hj]
  conv => lhs; rw [List.countP_congr (fun j _ => by rw [this j])]
  exact countP_split _ Std.ExtTreeMap.nodup_keys k (Std.ExtTreeMap.mem_keys.2 hk) _ _

/-- THE HOLDERS THE GATE COUNTS. With the key of each entity its own id,
    the gate counts the other keys that hold the name about the target. -/
theorem held_len (m : ids.Ids Entity) (hk : keyId m) (n : String) (t who : time.EntityId) :
    ((idsOf m).filterMap (pushH m n t who)).length =
      (Std.ExtTreeMap.keys m).countP (fun j => decide (j ≠ who.val) && holdsAt m n t j) := by
  unfold idsOf
  rw [List.filterMap_filterMap, List.length_filterMap_eq_countP]
  apply List.countP_congr
  intro k hkm
  rw [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_iff_isSome_getElem?] at hkm
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hkm
  have hid := hk k e he
  have hlt : k < 2 ^ UScalarTy.U32.numBits := by rw [← hid]; exact UScalar.hBounds e.id
  have hne : (e.id ≠ who) ↔ (k ≠ who.val) := by
    rw [← hid]
    constructor
    · intro h1 h2; exact h1 (by scalar_tac)
    · intro h1 h2; exact h1 (by rw [h2])
  simp only [dif_pos hlt, Option.bind_some, pushH, UScalar.ofNatCore_val_eq, holdsAt]
  by_cases h1 : k ≠ who.val
  · have := hne.2 h1
    by_cases h2 : holdsB n t e = true <;> simp [he, this, h1, h2]
  · have : ¬ e.id ≠ who := fun h => h1 (hne.1 h)
    simp only [ne_eq, Decidable.not_not] at h1 this
    subst h1
    simp [he, this]

/-- A CLEAN COUNT CHECK ON THE HOLDER SIDE. The other holders and the
    new one fit the limit. -/
theorem counts_holders_clean {w : World} {who : time.EntityId} {nm : String} {r : FactRules}
    {t : time.EntityId} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.counts_fit w who nm r t o = ok o') (he : o'.val = [])
    {sh : Shape} {hc tg : Count} {al : alloc.collections.btree.map.BTreeMap entity.EntityType
      (alloc.vec.Vec entity.EntityType) Global}
    (hr : r = .Linked sh hc tg al) {L : Std.U16} (hL : limitOf hc = some L) :
    ∃ hb, validate.holders_except w nm t who = ok hb ∧ hb.val.length < L.val := by
  subst hr
  unfold validate.counts_fit at h
  simp only [limit_eq, bind_tc_ok] at h
  rw [bind_eq_ok] at h
  obtain ⟨out1, h1, h⟩ := h
  have hr1 : out1.val <+: out1.val := List.prefix_refl _
  have p1 : out1.val <+: o'.val := grows_of (by grows) h
  have e1 := nil_of_prefix_nil p1 he
  simp [hL, lift] at h1
  rw [bind_eq_ok] at h1
  obtain ⟨hb, hhb, h1⟩ := h1
  refine ⟨hb, hhb, ?_⟩
  split at h1
  · rw [bind_eq_ok] at h1
    obtain ⟨_, _, h1⟩ := h1
    exact absurd e1 (push_ne h1)
  · rename_i hlt
    omega

/-- A START WITH NO FAULT fits the limit of holders. -/
theorem start_holders_clean {w : World} {who : time.EntityId} {nm : String} {v : Option Std.I64}
    {lt : Option time.EntityId} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.start w who nm v lt o = ok o') (he : o'.val = [])
    (r : FactRules) (hr : (w.vocabulary.names : names.Names FactRules)[nm]? = some r) :
    ∀ t, lt = some t → ∀ sh hc tg al, r = .Linked sh hc tg al → ∀ L, limitOf hc = some L →
      ∃ hb, validate.holders_except w nm t who = ok hb ∧ hb.val.length < L.val := by
  unfold validate.start at h
  rw [bind_eq_ok] at h
  obtain ⟨⟨holder, out1⟩, h1, h⟩ := h
  simp only [FactVocabulary.rules_key, names.Names.get_key] at h
  simp [hr] at h
  rw [bind_eq_ok] at h
  obtain ⟨out2, h2, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out3, h3, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out4, h4, h⟩ := h
  have hr4 : out4.val <+: out4.val := List.prefix_refl _
  have p5 : out4.val <+: o'.val := grows_of (by grows) h
  have e4 := nil_of_prefix_nil p5 he
  intro t ht sh hc tg al hrl L hL
  subst ht hrl
  simp only [takesT, if_true] at h4
  rw [bind_eq_ok] at h4
  obtain ⟨_, _, h4⟩ := h4
  rw [bind_eq_ok] at h4
  obtain ⟨out5, h5, h4⟩ := h4
  rw [bind_eq_ok] at h4
  obtain ⟨out6, h6, h4⟩ := h4
  have hr6 : out6.val <+: out6.val := List.prefix_refl _
  have p6 : out6.val <+: out4.val := grows_of (by grows) h4
  have e6 := nil_of_prefix_nil p6 e4
  rw [bind_eq_ok] at h6
  obtain ⟨_, _, h6⟩ := h6
  rw [bind_eq_ok] at h6
  obtain ⟨out7, _, h6⟩ := h6
  exact counts_holders_clean h6 e6 rfl hL

/-! ## The holders law -/

theorem keyId_erase {m : ids.Ids Entity} (h : keyId m) (k : Nat) :
    keyId (Std.ExtTreeMap.erase m k) := by
  intro j e hj
  rw [Std.ExtTreeMap.getElem?_erase] at hj
  split at hj
  · simp at hj
  · exact h j e hj

theorem keyId_insert {m : ids.Ids Entity} (h : keyId m) (k : Nat) (row : Entity)
    (hr : row.id.val = k) : keyId (Std.ExtTreeMap.insert m k row) := by
  intro j e hj
  rw [Std.ExtTreeMap.getElem?_insert] at hj
  split at hj
  · rename_i hkj
    simp only [Option.some.injEq] at hj; subst hj
    rw [hr]; simpa using hkj
  · exact h j e hj

/-- APPLY KEEPS THE KEY OF EACH ENTITY ITS OWN ID. -/
theorem apply_keyId (m : ids.Ids Entity) (v : FactVocabulary) (ev : Event) (m' : ids.Ids Entity)
    (h : keyId m) (ha : World.apply m v ev = ok m') : keyId m' := by
  unfold World.apply at ha
  cases hk : ev.kind <;> simp only [hk] at ha
  case EntityCreated id ty nm =>
    simp only [ids.Ids.contains, bind_tc_ok] at ha
    split at ha
    · simp only [ok.injEq] at ha; subst ha; exact h
    · simp only [alloc.string.String.Insts.CoreCloneClone.clone, time.TimeSpan.open,
        ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
      subst ha
      exact keyId_insert h _ _ rfl
  case EntityDestroyed id =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[id.val]? with
    | none => simp [hr] at ha; subst ha; exact keyId_erase h _
    | some row =>
      have hid := h _ _ hr
      simp [hr, ids.Ids.insert] at ha
      split at ha
      all_goals
        simp only [bind_tc_ok, ok.injEq] at ha
        subst ha
        exact keyId_insert (keyId_erase h _) _ _ hid
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨_, _, ha⟩ := ha
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact keyId_erase h _
    | some row =>
      have hid := h _ _ hr
      simp [hr, ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
      repeat (rw [bind_eq_ok] at ha; obtain ⟨_, _, ha⟩ := ha)
      simp only [ok.injEq] at ha
      subst ha
      exact keyId_insert (keyId_erase h _) _ _ hid
  case FactUpdate who nm lt fr tv =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact keyId_erase h _
    | some row =>
      have hid := h _ _ hr
      simp [hr, ids.Ids.insert] at ha
      repeat (rw [bind_eq_ok] at ha; obtain ⟨_, _, ha⟩ := ha)
      simp only [ok.injEq] at ha
      subst ha
      exact keyId_insert (keyId_erase h _) _ _ hid
  case FactEnd who nm lt =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact keyId_erase h _
    | some row =>
      have hid := h _ _ hr
      simp [hr, ids.Ids.insert] at ha
      repeat (rw [bind_eq_ok] at ha; obtain ⟨_, _, ha⟩ := ha)
      simp only [ok.injEq] at ha
      subst ha
      exact keyId_insert (keyId_erase h _) _ _ hid


/-- Take out a key that the map does not hold: nothing changes. -/
theorem erase_absent (m : ids.Ids Entity) (k : Nat)
    (hr : (m : Std.ExtTreeMap Nat Entity compare)[k]? = none) :
    Std.ExtTreeMap.erase m k = m := by
  apply Std.ExtTreeMap.ext_getElem?
  intro j
  rw [Std.ExtTreeMap.getElem?_erase]
  split
  · rename_i hkj
    have : k = j := by simpa using hkj
    subst this; exact hr.symm
  · rfl

/-- A new entity with no fact about the target leaves the count. -/
theorem count_new (m : ids.Ids Entity) (k : Nat) (row : Entity)
    (hk : k ∉ (m : Std.ExtTreeMap Nat Entity compare)) (n : String) (t : time.EntityId)
    (hb : holdsB n t row = false) :
    holdersCount (Std.ExtTreeMap.insert m k row) n t = holdersCount m n t := by
  unfold holdersCount
  have hperm : (Std.ExtTreeMap.keys (Std.ExtTreeMap.insert m k row)).Perm
      (k :: Std.ExtTreeMap.keys m) := by
    rw [List.perm_ext_iff_of_nodup Std.ExtTreeMap.nodup_keys
      (List.nodup_cons.2 ⟨fun h => hk (Std.ExtTreeMap.mem_keys.1 h), Std.ExtTreeMap.nodup_keys⟩)]
    intro j
    by_cases hj : j = k
    · subst hj; simp
    · simp [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_insert, hj, Ne.symm hj]
  rw [hperm.countP_eq, List.countP_cons]
  have hat : holdsAt (Std.ExtTreeMap.insert m k row) n t k = false := by
    simp [holdsAt, hb]
  rw [hat]
  simp only [Bool.false_eq_true, if_false, Nat.add_zero]
  apply List.countP_congr
  intro j hj
  have hne : k ≠ j := fun h => hk (h ▸ Std.ExtTreeMap.mem_keys.1 hj)
  simp [holdsAt, Std.ExtTreeMap.getElem?_insert, hne]

/-- Replace one entity with a row that holds less: the count does not grow. -/
theorem count_mono (m : ids.Ids Entity) (k : Nat) (row row' : Entity)
    (hr : (m : Std.ExtTreeMap Nat Entity compare)[k]? = some row) (n : String) (t : time.EntityId)
    (hle : holdsB n t row' = true → holdsB n t row = true) :
    holdersCount (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k row') n t ≤
      holdersCount m n t := by
  have hk : k ∈ (m : Std.ExtTreeMap Nat Entity compare) := by
    rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hr]; rfl
  rw [count_replace m k row' hk, count_before m k row hr]
  cases h1 : holdsB n t row' <;> cases h2 : holdsB n t row <;> simp_all

/-- A row whose facts all sit in slots of the old row holds less. -/
theorem holds_of_slots {n : String} {t : time.EntityId} {row row' : Entity}
    (hs : ∀ x ∈ row'.facts.val, ∃ y ∈ row.facts.val, slotOf x = slotOf y) :
    holdsB n t row' = true → holdsB n t row = true := by
  simp only [holdsB, List.any_eq_true]
  rintro ⟨x, hx, hin⟩
  obtain ⟨y, hy, hxy⟩ := hs x hx
  exact ⟨y, hy, by simpa [inSlot, hxy] using hin⟩


/-- What a clean gate says about the holders of a start. -/
def holdClean (w : World) : EventKind → Prop
  | .FactStart who nm _ lt =>
    ∀ r, (w.vocabulary.names : names.Names FactRules)[nm]? = some r →
      ∀ t, lt = some t → ∀ sh hc tg al, r = .Linked sh hc tg al → ∀ L, limitOf hc = some L →
        ∃ hb, validate.holders_except w nm t who = ok hb ∧ hb.val.length < L.val
  | _ => True

theorem validate_holders {w : World} {t : time.Tick} {k : EventKind}
    {f : alloc.vec.Vec reject.Rejection}
    (h : validate.validate w t k = ok f) (he : f.val = []) : holdClean w k := by
  unfold validate.validate at h
  rw [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out, _, h⟩ := h
  cases k with
  | FactStart who nm value lt => exact fun r hr => start_holders_clean h he r hr
  | _ => trivial

/-- A name with a limit of holders has at most that many holders of
    each target. -/
def holdersOk (v : FactVocabulary) (m : ids.Ids Entity) : Prop :=
  ∀ (n : String) (t : time.EntityId) (sh : Shape) (hc tg : Count)
    (al : alloc.collections.btree.map.BTreeMap entity.EntityType (alloc.vec.Vec entity.EntityType) Global)
    (L : Std.U16), (v.names : names.Names FactRules)[n]? = some (.Linked sh hc tg al) →
    limitOf hc = some L → holdersCount m n t ≤ L.val

/-- APPLY KEEPS THE LIMIT OF HOLDERS, for an event with clean holders. -/
theorem apply_holders (w : World) (ev : Event) (m' : ids.Ids Entity)
    (h : holdersOk w.vocabulary w.entities) (hk : keyId w.entities)
    (hc : holdClean w ev.kind) (ha : World.apply w.entities w.vocabulary ev = ok m') :
    holdersOk w.vocabulary m' := by
  unfold World.apply at ha
  cases hkd : ev.kind <;> simp only [hkd] at ha <;> rw [hkd] at hc
  case EntityCreated id ty nm =>
    simp only [ids.Ids.contains, bind_tc_ok] at ha
    split at ha
    · simp only [ok.injEq] at ha; subst ha; exact h
    · rename_i hnot
      simp only [alloc.string.String.Insts.CoreCloneClone.clone, time.TimeSpan.open,
        ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
      subst ha
      intro n t sh hcn tg al L hn hL
      rw [count_new _ _ _ (by simpa using hnot) n t (by simp [holdsB, alloc.vec.Vec.new])]
      exact h n t sh hcn tg al L hn hL
  case EntityDestroyed id =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]? with
    | none => simp [hr] at ha; subst ha; rw [erase_absent _ _ hr]; exact h
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      split at ha
      all_goals
        simp only [bind_tc_ok, ok.injEq] at ha
        subst ha
        intro n t sh hcn tg al L hn hL
        refine le_trans (count_mono _ _ row _ hr n t ?_) (h n t sh hcn tg al L hn hL)
        exact holds_of_slots (fun x hx => ⟨x, hx, rfl⟩)
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨wide, _, ha⟩ := ha
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; rw [erase_absent _ _ hr]; exact h
    | some row =>
      simp [hr, ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨v1, hv1, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      intro n t sh hcn tg al L hn hL
      have hsub : ∀ x ∈ vf.val, x ∈ row.facts.val := by
        intro x hx
        cases wide
        · simp only [Bool.false_eq_true, if_false, world.drop_slot] at hvf
          rw [drop_slot_ok hvf, List.mem_filter] at hx; exact hx.1
        · simp only [if_true, world.drop_name] at hvf
          rw [drop_name_ok hvf, List.mem_filter] at hx; exact hx.1
      by_cases hslot : nm = n ∧ lt = some t
      · -- The slot of the event: the others fit below the limit, and
        -- the new holder takes the last place.
        obtain ⟨rfl, rfl⟩ := hslot
        obtain ⟨hb, hhb, hlt⟩ := hc _ hn t rfl sh hcn tg al rfl L hL
        have hmem : who.val ∈ (w.entities : Std.ExtTreeMap Nat Entity compare) := by
          rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hr]; rfl
        rw [count_replace _ _ _ hmem]
        have hlen := held_len w.entities hk nm t who
        rw [← holders_except_ok hhb] at hlen
        rw [← hlen]
        split <;> omega
      · -- Another slot: the new fact is not in it.
        refine le_trans (count_mono _ _ row _ hr n t ?_) (h n t sh hcn tg al L hn hL)
        simp only [holdsB, push_val_any hv1, List.any_append, List.any_cons, List.any_nil,
          Bool.or_false, Bool.or_eq_true, List.any_eq_true]
        rintro (⟨x, hx, hin⟩ | hin)
        · exact ⟨x, hsub x hx, hin⟩
        · exfalso
          simp [inSlot, slotOf] at hin
          exact hslot ⟨hin.1, hin.2⟩
  case FactUpdate who nm lt fr tv =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; rw [erase_absent _ _ hr]; exact h
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨o1, ho1, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      intro n t sh hcn tg al L hn hL
      refine le_trans (count_mono _ _ row _ hr n t ?_) (h n t sh hcn tg al L hn hL)
      apply holds_of_slots
      cases o1 with
      | none =>
        simp only [ok.injEq] at hvf; subst hvf
        exact fun x hx => ⟨x, hx, rfl⟩
      | some i =>
        obtain ⟨_, ho1', hlt⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
          (slot_index_spec row.facts.deref nm lt)
        rw [ho1] at ho1'
        simp only [ok.injEq] at ho1'
        subst ho1'
        have hi : i.val < row.facts.val.length := by
          simpa [alloc.vec.Vec.deref] using (hlt.1 i rfl).1
        simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize] at hvf
        simp [hi] at hvf
        subst hvf
        intro x hx
        simp only [alloc.vec.Vec.set_val_eq, List.set_set] at hx
        rcases List.mem_or_eq_of_mem_set hx with hx | hx
        · exact ⟨x, hx, rfl⟩
        · exact ⟨_, List.getElem_mem hi, by rw [hx]; simp [slotOf]⟩
  case FactEnd who nm lt =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; rw [erase_absent _ _ hr]; exact h
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      intro n t sh hcn tg al L hn hL
      refine le_trans (count_mono _ _ row _ hr n t ?_) (h n t sh hcn tg al L hn hL)
      apply holds_of_slots
      intro x hx
      rw [drop_slot_ok hvf, List.mem_filter] at hx
      exact ⟨x, hx.1, rfl⟩


theorem reachP_holders {w u : World} (hr : ReachP w u)
    (h : holdersOk w.vocabulary w.entities ∧ keyId w.entities) :
    holdersOk u.vocabulary u.entities ∧ keyId u.entities := by
  induction hr with
  | refl => exact h
  | @step u1 u2 t k r _ hp ih =>
    cases r with
    | Err f => rw [(propose_err u1 u2 t k f hp).1]; exact ih
    | Ok id =>
      obtain ⟨⟨f, hv, he⟩, hc⟩ := propose_ok u1 u2 t k id hp
      obtain ⟨_, _, hvoc⟩ := commit_ok hc
      rw [hvoc]
      exact ⟨apply_holders u1 ⟨id, t, k⟩ _ ih.1 ih.2 (validate_holders hv he) (commit_apply hc),
        apply_keyId _ _ _ _ ih.2 (commit_apply hc)⟩

/-- A TARGET NEVER HAS MORE HOLDERS THAN ITS COUNT ALLOWS. In every
    world that proposals build from an empty world, a name with a limit
    of holders has at most that many holders of each target. -/
theorem every_proposed_world_holders (v : FactVocabulary) (w0 w : World)
    (h0 : World.new v = ok w0) (hr : ReachP w0 w) :
    holdersOk w.vocabulary w.entities := by
  apply (reachP_holders hr _).1
  simp only [World.new, ids.Ids.new, EventHistory.new, bind_tc_ok, ok.injEq] at h0
  subst h0
  refine ⟨fun n t _ _ _ _ _ _ _ => by
    simp [holdersCount, Std.ExtTreeMap.keys_eq_nil_iff.2 rfl], fun k _ hk => by simp at hk⟩

end hourglass
