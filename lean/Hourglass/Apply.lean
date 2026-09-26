-- The rung 4a laws: the rules inside `apply`.
--
-- One fact per slot, and an entity never vanishes. With the Reach
-- relation of World.lean, both laws hold for every world that commits
-- and proposals build, with or without `validate`.
import Hourglass.World

open Aeneas Aeneas.Std Result

namespace hourglass

open world event fact entity

/-! ## The slot of a fact, and the drop loops -/

/-- The slot of a fact: its name and its target. -/
def slotOf (f : Fact) : String × Option time.EntityId := (f.name, f.linked_to)

/-- `in_slot`, as a pure function. -/
def inSlot (f : Fact) (n : String) (l : Option time.EntityId) : Bool :=
  decide (slotOf f = (n, l))

@[simp] theorem in_slot_eq (f : Fact) (n : String) (l : Option time.EntityId) :
    world.in_slot f n l = ok (inSlot f n l) := by
  unfold world.in_slot inSlot slotOf
  simp only [alloc.string.String.Insts.CoreCmpPartialEqString.eq, bind_tc_ok]
  by_cases hn : f.name = n
  · cases hl : f.linked_to <;> cases l <;>
      simp [hn, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
        time.EntityId.Insts.CoreCmpPartialEqEntityId.eq]
  · simp [hn]

@[step] theorem in_slot_spec (f : Fact) (n : String) (l : Option time.EntityId) :
    world.in_slot f n l ⦃ b => b = inSlot f n l ⦄ := by
  simp

@[step] theorem remove_spec {T : Type} (A : Type) (v : alloc.vec.Vec T) (i : Usize)
    (h : i.val < v.length) :
    alloc.vec.Vec.remove A v i ⦃ x v' => x = v.val[i.val] ∧
      v'.val = v.val.take i.val ++ v.val.drop (i.val + 1) ⦄ := by
  have h' : i.val < v.val.length := by simpa using h
  simp [alloc.vec.Vec.remove, h', List.eraseIdx_eq_take_drop_succ]

/-- The drop loop, with a filter as its spec. -/
@[step] theorem drop_slot_loop_spec (facts : alloc.vec.Vec Fact) (n : String)
    (l : Option time.EntityId) (i : Usize) (hi : i.val ≤ facts.length) :
    world.drop_slot_loop facts n l i
      ⦃ r => r.val = facts.val.take i.val ++
        (facts.val.drop i.val).filter (fun f => !inSlot f n l) ⦄ := by
  unfold world.drop_slot_loop
  step*
  · -- The loop goes on at `i` over a shorter list.
    have h1 := congrArg List.length __post1
    simp only [List.length_append, List.length_take, List.length_drop] at h1
    scalar_tac
  · -- The fact at `i` is in the slot, and the loop dropped it.
    have hlt : i.val < facts.val.length := by scalar_tac
    have hin : inSlot facts.val[i.val] n l = true := by simp_all
    rw [r_post, __post1, List.drop_eq_getElem_cons hlt, List.filter_cons, hin]
    simp [List.take_append_of_le_length (show i.val ≤ (List.take i.val facts.val).length by
        simp; omega),
      List.drop_append_of_le_length (show i.val ≤ (List.take i.val facts.val).length by
        simp; omega)]
  · -- The fact at `i` stays.
    have hlt : i.val < facts.val.length := by scalar_tac
    have hout : inSlot facts.val[i.val] n l = false := by simp_all
    rw [r_post, i2_post, List.drop_eq_getElem_cons hlt, List.filter_cons, hout,
      List.take_succ_eq_append_getElem hlt]
    simp only [Bool.not_false, if_true, List.append_assoc, List.singleton_append]
  · have hle : facts.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hle, List.take_of_length_le hle]
termination_by facts.length - i.val
decreasing_by all_goals (simp_all; scalar_tac)

@[step] theorem string_eq_spec (a b : String) :
    alloc.string.String.Insts.CoreCmpPartialEqString.eq a b ⦃ r => r = decide (a = b) ⦄ := by
  simp [alloc.string.String.Insts.CoreCmpPartialEqString.eq]

/-- The name loop, with a filter as its spec. -/
@[step] theorem drop_name_loop_spec (facts : alloc.vec.Vec Fact) (n : String)
    (i : Usize) (hi : i.val ≤ facts.length) :
    world.drop_name_loop facts n i
      ⦃ r => r.val = facts.val.take i.val ++
        (facts.val.drop i.val).filter (fun f => !decide (f.name = n)) ⦄ := by
  unfold world.drop_name_loop
  step*
  · -- The loop goes on at `i` over a shorter list.
    have h1 := congrArg List.length __post1
    simp only [List.length_append, List.length_take, List.length_drop] at h1
    scalar_tac
  · -- The fact at `i` has the name, and the loop dropped it.
    have hlt : i.val < facts.val.length := by scalar_tac
    have hin : decide (facts.val[i.val].name = n) = true := by simp_all
    rw [r_post, __post1, List.drop_eq_getElem_cons hlt, List.filter_cons, hin]
    simp [List.take_append_of_le_length (show i.val ≤ (List.take i.val facts.val).length by
        simp; omega),
      List.drop_append_of_le_length (show i.val ≤ (List.take i.val facts.val).length by
        simp; omega)]
  · -- The fact at `i` stays.
    have hlt : i.val < facts.val.length := by scalar_tac
    have hout : decide (facts.val[i.val].name = n) = false := by simp_all
    rw [r_post, i2_post, List.drop_eq_getElem_cons hlt, List.filter_cons, hout,
      List.take_succ_eq_append_getElem hlt]
    simp only [Bool.not_false, if_true, List.append_assoc, List.singleton_append]
  · have hle : facts.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hle, List.take_of_length_le hle]
termination_by facts.length - i.val
decreasing_by all_goals (simp_all; scalar_tac)


@[step] theorem drop_slot_spec (facts : alloc.vec.Vec Fact) (n : String)
    (l : Option time.EntityId) :
    world.drop_slot facts n l ⦃ r => r.val = facts.val.filter (fun f => !inSlot f n l) ⦄ := by
  unfold world.drop_slot
  step*
  simp_all

@[step] theorem drop_name_spec (facts : alloc.vec.Vec Fact) (n : String) :
    world.drop_name facts n ⦃ r => r.val = facts.val.filter (fun f => !decide (f.name = n)) ⦄ := by
  unfold world.drop_name
  step*
  simp_all

/-- The slot search answers a place inside the list, or nothing. -/
@[step] theorem slot_index_loop_spec (facts : Slice Fact) (n : String)
    (l : Option time.EntityId) (i : Usize) :
    world.slot_index_loop facts n l i
      ⦃ o => ∀ j, o = some j → j.val < facts.length ⦄ := by
  unfold world.slot_index_loop
  step*
termination_by facts.length - i.val
decreasing_by scalar_tac

@[step] theorem slot_index_spec (facts : Slice Fact) (n : String) (l : Option time.EntityId) :
    world.slot_index facts n l ⦃ o => ∀ j, o = some j → j.val < facts.length ⦄ := by
  unfold world.slot_index
  step*

/-! ## One fact per slot -/

theorem push_val_any {T : Type} {v v' : alloc.vec.Vec T} {x : T}
    (h : alloc.vec.Vec.push v x = ok v') : v'.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · simp only [ok.injEq] at h
    subst h
    simp [alloc.vec.Vec.from_val]
  · simp at h

theorem bind_eq_ok {α β : Type} (x : Result α) (f : α → Result β) (y : β) :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp

/-- The slots of an entity, in the order of its facts. -/
def slots (e : Entity) : List (String × Option time.EntityId) := e.facts.val.map slotOf

/-- No entity holds two facts in one slot. -/
def oneFactPerSlot (m : ids.Ids Entity) : Prop :=
  ∀ (k : Nat) (e : Entity), (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e →
    (slots e).Nodup

theorem ofps_erase {m : ids.Ids Entity} (h : oneFactPerSlot m) (k : Nat) :
    oneFactPerSlot (Std.ExtTreeMap.erase m k) := by
  intro j e hj
  rw [Std.ExtTreeMap.getElem?_erase] at hj
  split at hj
  · simp at hj
  · exact h j e hj

theorem ofps_insert {m : ids.Ids Entity} (h : oneFactPerSlot m) (k : Nat) (row : Entity)
    (hr : (slots row).Nodup) : oneFactPerSlot (Std.ExtTreeMap.insert m k row) := by
  intro j e hj
  rw [Std.ExtTreeMap.getElem?_insert] at hj
  split at hj
  · simp only [Option.some.injEq] at hj; subst hj; exact hr
  · exact h j e hj

theorem slots_filter_nodup (row : Entity) (p : Fact → Bool) (hr : (slots row).Nodup) :
    ((row.facts.val.filter p).map slotOf).Nodup :=
  List.Nodup.sublist (List.Sublist.map slotOf List.filter_sublist) hr

theorem drop_slot_ok {facts r : alloc.vec.Vec Fact} {n : String} {l : Option time.EntityId}
    (h : world.drop_slot_loop facts n l 0#usize = ok r) :
    r.val = facts.val.filter (fun f => !inSlot f n l) := by
  obtain ⟨r', h1, h2⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
    (drop_slot_loop_spec facts n l 0#usize (by simp))
  rw [h] at h1; simp only [ok.injEq] at h1; subst h1
  simpa using h2

theorem drop_name_ok {facts r : alloc.vec.Vec Fact} {n : String}
    (h : world.drop_name_loop facts n 0#usize = ok r) :
    r.val = facts.val.filter (fun f => !decide (f.name = n)) := by
  obtain ⟨r', h1, h2⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
    (drop_name_loop_spec facts n 0#usize (by simp))
  rw [h] at h1; simp only [ok.injEq] at h1; subst h1
  simpa using h2

/-- A write that keeps the name and the target keeps the slots. -/
theorem map_set_self_slot (l : List Fact) (i : Nat) (hi : i < l.length) :
    (l.map slotOf).set i (l[i].name, l[i].linked_to) = l.map slotOf := by
  have : (l[i].name, l[i].linked_to) = (l.map slotOf)[i]'(by simpa using hi) := by
    simp [slotOf]
  rw [this, List.set_getElem_self]

/-- APPLY KEEPS ONE FACT PER SLOT. If no entity holds two facts in one
    slot, then after any event that `apply` folds in, still none does. -/
theorem apply_one_fact_per_slot (m : ids.Ids Entity) (v : FactVocabulary) (ev : Event)
    (m' : ids.Ids Entity) (h : oneFactPerSlot m) (ha : World.apply m v ev = ok m') :
    oneFactPerSlot m' := by
  unfold World.apply at ha
  cases hk : ev.kind <;> simp only [hk] at ha
  case EntityCreated id ty nm =>
    simp only [ids.Ids.contains, bind_tc_ok] at ha
    split at ha
    · simp only [ok.injEq] at ha; subst ha; exact h
    · simp only [alloc.string.String.Insts.CoreCloneClone.clone, time.TimeSpan.open,
        ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
      subst ha
      exact ofps_insert h _ _ (by simp [slots, alloc.vec.Vec.new])
  case EntityDestroyed id =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[id.val]? with
    | none =>
      simp [hr] at ha; subst ha; exact ofps_erase h _
    | some row =>
      have hrow : (slots row).Nodup := h _ _ hr
      simp [hr, ids.Ids.insert] at ha
      split at ha
      all_goals
        simp only [bind_tc_ok, ok.injEq] at ha
        subst ha
        exact ofps_insert (ofps_erase h _) _ _ (by simpa [slots] using hrow)
  case FactEnd who nm lt =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact ofps_erase h _
    | some row =>
      have hrow := h _ _ hr
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply ofps_insert (ofps_erase h _)
      simp only [slots, drop_slot_ok hvf]
      exact slots_filter_nodup row _ hrow
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨wide, _, ha⟩ := ha
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact ofps_erase h _
    | some row =>
      have hrow := h _ _ hr
      simp [hr, ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨v1, hv1, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply ofps_insert (ofps_erase h _)
      -- The facts that stay: a filter of the old ones, and none of them
      -- sits in the slot of the new fact.
      have hkeep : (vf.val.map slotOf).Nodup ∧ ∀ g ∈ vf.val, slotOf g ≠ (nm, lt) := by
        cases wide
        · simp only [Bool.false_eq_true, if_false, world.drop_slot] at hvf
          rw [drop_slot_ok hvf]
          refine ⟨slots_filter_nodup row _ hrow, ?_⟩
          intro g hg
          rw [List.mem_filter] at hg
          simpa [inSlot] using hg.2
        · simp only [if_true, world.drop_name] at hvf
          rw [drop_name_ok hvf]
          refine ⟨slots_filter_nodup row _ hrow, ?_⟩
          intro g hg
          rw [List.mem_filter] at hg
          simp only [slotOf, ne_eq, Prod.mk.injEq, not_and]
          intro hn
          simp [hn] at hg
      simp only [slots, push_val_any hv1, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨hkeep.1, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
      exact hkeep.2 g hg
  case FactUpdate who nm lt fr tv =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact ofps_erase h _
    | some row =>
      have hrow := h _ _ hr
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨o1, ho1, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply ofps_insert (ofps_erase h _)
      suffices hs : vf.val.map slotOf = row.facts.val.map slotOf by
        simpa [slots, hs] using hrow
      cases o1 with
      | none => simp only [ok.injEq] at hvf; subst hvf; rfl
      | some i =>
        obtain ⟨_, ho1', hlt⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
          (slot_index_spec row.facts.deref nm lt)
        rw [ho1] at ho1'
        simp only [ok.injEq] at ho1'
        subst ho1'
        have hi : i.val < row.facts.val.length := by
          simpa [alloc.vec.Vec.deref] using hlt i rfl
        simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize] at hvf
        simp [hi] at hvf
        subst hvf
        simp [List.map_set, slotOf]
        exact map_set_self_slot _ _ hi

/-! ## An entity never vanishes -/

/-- The ids a map holds. -/
def holds (m : ids.Ids Entity) (k : Nat) : Prop := k ∈ (m : Std.ExtTreeMap Nat Entity compare)

/-- APPLY NEVER REMOVES AN ENTITY. A destroyed entity stays, with its
    span closed. -/
theorem apply_keeps_ids (m : ids.Ids Entity) (v : FactVocabulary) (ev : Event)
    (m' : ids.Ids Entity) (ha : World.apply m v ev = ok m') :
    ∀ k, holds m k → holds m' k := by
  intro k hk
  unfold holds at *
  unfold World.apply at ha
  -- In every case, the result is the map, the map with one more id,
  -- or the map with one id taken out and put back.
  have back : ∀ (j : Nat) (row : Entity),
      k ∈ Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m j) j row := by
    intro j row
    rw [Std.ExtTreeMap.mem_insert, Std.ExtTreeMap.mem_erase]
    by_cases hj : compare j k = .eq
    · exact Or.inl hj
    · exact Or.inr ⟨hj, hk⟩
  have gone : ∀ j : Nat, (m : Std.ExtTreeMap Nat Entity compare)[j]? = none →
      k ∈ Std.ExtTreeMap.erase m j := by
    intro j hj
    rw [Std.ExtTreeMap.mem_erase]
    refine ⟨?_, hk⟩
    intro he
    have : j = k := by simpa using he
    subst this
    rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hj] at hk
    simp at hk
  cases hkd : ev.kind <;> simp only [hkd] at ha
  case EntityCreated id ty nm =>
    simp only [ids.Ids.contains, bind_tc_ok] at ha
    split at ha
    · simp only [ok.injEq] at ha; subst ha; exact hk
    · simp only [alloc.string.String.Insts.CoreCloneClone.clone, time.TimeSpan.open,
        ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
      subst ha
      rw [Std.ExtTreeMap.mem_insert]; exact Or.inr hk
  case EntityDestroyed id =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[id.val]? with
    | none => simp [hr] at ha; subst ha; exact gone _ hr
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      split at ha
      all_goals
        simp only [bind_tc_ok, ok.injEq] at ha
        subst ha
        exact back _ _
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨_, _, ha⟩ := ha
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact gone _ hr
    | some row =>
      simp [hr, ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
      repeat (rw [bind_eq_ok] at ha; obtain ⟨_, _, ha⟩ := ha)
      simp only [ok.injEq] at ha
      subst ha
      exact back _ _
  case FactUpdate who nm lt fr tv =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact gone _ hr
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      repeat (rw [bind_eq_ok] at ha; obtain ⟨_, _, ha⟩ := ha)
      simp only [ok.injEq] at ha
      subst ha
      exact back _ _
  case FactEnd who nm lt =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact gone _ hr
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      repeat (rw [bind_eq_ok] at ha; obtain ⟨_, _, ha⟩ := ha)
      simp only [ok.injEq] at ha
      subst ha
      exact back _ _

/-! ## Every world that commits build -/

/-- A commit that succeeds passed its entities through `apply`. -/
theorem commit_apply {w w' : World} {t : time.Tick} {k : EventKind} {id : time.EventId}
    (hc : World.commit w t k = ok (id, w')) :
    World.apply w.entities w.vocabulary ⟨id, t, k⟩ = ok w'.entities := by
  unfold World.commit at hc
  cases hn : EventHistory.next_id w.history
  case ret id0 =>
    simp only [hn, bind_tc_ok] at hc
    cases ha : World.apply w.entities w.vocabulary ⟨id0, t, k⟩
    case ret bm =>
      simp only [ha, bind_tc_ok, EventHistory.append] at hc
      cases hp : alloc.vec.Vec.push w.history ⟨id0, t, k⟩
      case ret eh =>
        simp only [hp, bind_tc_ok, time.Tick.Insts.CoreCmpPartialOrdTick.gt] at hc
        split at hc <;> simp only [ok.injEq, Prod.mk.injEq] at hc <;>
          obtain ⟨rfl, rfl⟩ := hc <;> exact ha
      all_goals simp [hp] at hc
    all_goals simp [ha] at hc
  all_goals simp [hn] at hc

theorem reach_one_fact_per_slot {w u : World} (hr : Reach w u)
    (h : oneFactPerSlot w.entities) : oneFactPerSlot u.entities := by
  induction hr with
  | refl => exact h
  | step _ hc ih => exact apply_one_fact_per_slot _ _ _ _ ih (commit_apply hc)

theorem reach_keeps_ids {w u : World} (hr : Reach w u) :
    ∀ k, holds w.entities k → holds u.entities k := by
  induction hr with
  | refl => exact fun _ hk => hk
  | step _ hc ih => exact fun k hk => apply_keeps_ids _ _ _ _ (commit_apply hc) k (ih k hk)

/-- ONE FACT PER SLOT, IN EVERY WORLD. A world that commits and
    proposals build from an empty world never holds two facts in one
    slot. This holds with or without `validate`. -/
theorem every_world_one_fact_per_slot (v : FactVocabulary) (w0 w : World)
    (h0 : World.new v = ok w0) (hr : Reach w0 w) : oneFactPerSlot w.entities := by
  apply reach_one_fact_per_slot hr
  simp only [World.new, ids.Ids.new, EventHistory.new, bind_tc_ok, ok.injEq] at h0
  subst h0
  intro k e hk
  simp at hk

/-- AN ENTITY NEVER VANISHES. Every entity of a world stays in every
    world that later commits and proposals build from it. -/
theorem entities_never_vanish {w u : World} (hr : Reach w u) :
    ∀ k, holds w.entities k → holds u.entities k :=
  reach_keeps_ids hr

/-! ## A single-target name holds one fact -/

/-- The number of facts of one name. -/
def countName (e : Entity) (n : String) : Nat := e.facts.val.countP (fun f => decide (f.name = n))

/-- Every name that allows one target at a time holds at most one fact
    on each entity. For example, `located_in`: an entity sits in one
    place at a time. -/
def oneTarget (v : FactVocabulary) (m : ids.Ids Entity) : Prop :=
  ∀ (k : Nat) (e : Entity) (n : String), (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e →
    world.single_target v n = ok true → countName e n ≤ 1

theorem ot_erase {v : FactVocabulary} {m : ids.Ids Entity} (h : oneTarget v m) (k : Nat) :
    oneTarget v (Std.ExtTreeMap.erase m k) := by
  intro j e n hj hs
  rw [Std.ExtTreeMap.getElem?_erase] at hj
  split at hj
  · simp at hj
  · exact h j e n hj hs

theorem ot_insert {v : FactVocabulary} {m : ids.Ids Entity} (h : oneTarget v m) (k : Nat)
    (row : Entity) (hr : ∀ n, world.single_target v n = ok true → countName row n ≤ 1) :
    oneTarget v (Std.ExtTreeMap.insert m k row) := by
  intro j e n hj hs
  rw [Std.ExtTreeMap.getElem?_insert] at hj
  split at hj
  · simp only [Option.some.injEq] at hj; subst hj; exact hr n hs
  · exact h j e n hj hs

theorem countP_filter_le (l : List Fact) (p : Fact → Bool) (n : String) :
    (l.filter p).countP (fun f => decide (f.name = n)) ≤ l.countP (fun f => decide (f.name = n)) :=
  List.Sublist.countP_le List.filter_sublist

/-- APPLY KEEPS ONE FACT PER SINGLE-TARGET NAME. -/
theorem apply_one_target (m : ids.Ids Entity) (v : FactVocabulary) (ev : Event)
    (m' : ids.Ids Entity) (h : oneTarget v m) (ha : World.apply m v ev = ok m') :
    oneTarget v m' := by
  unfold World.apply at ha
  cases hk : ev.kind <;> simp only [hk] at ha
  case EntityCreated id ty nm =>
    simp only [ids.Ids.contains, bind_tc_ok] at ha
    split at ha
    · simp only [ok.injEq] at ha; subst ha; exact h
    · simp only [alloc.string.String.Insts.CoreCloneClone.clone, time.TimeSpan.open,
        ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
      subst ha
      exact ot_insert h _ _ (fun n _ => by simp [countName, alloc.vec.Vec.new])
  case EntityDestroyed id =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[id.val]? with
    | none => simp [hr] at ha; subst ha; exact ot_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      split at ha
      all_goals
        simp only [bind_tc_ok, ok.injEq] at ha
        subst ha
        exact ot_insert (ot_erase h _) _ _ (fun n hs => by
          simpa [countName] using h _ _ n hr hs)
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨wide, hwide, ha⟩ := ha
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact ot_erase h _
    | some row =>
      simp [hr, ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨v1, hv1, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply ot_insert (ot_erase h _)
      intro n hs
      simp only [countName, push_val_any hv1, List.countP_append]
      by_cases hn : nm = n
      · -- The name of the event: it is single, so `apply` dropped
        -- every old fact of it, and one new fact stays.
        subst hn
        rw [hwide] at hs
        simp only [ok.injEq] at hs
        subst hs
        simp only [if_true, world.drop_name] at hvf
        rw [drop_name_ok hvf]
        simp [List.countP_eq_zero]
      · -- Another name: the new fact does not count, and the drop only
        -- takes facts away.
        have hold := h _ _ n hr hs
        have hnew : List.countP (fun f : Fact => decide (f.name = n))
            [({ «name» := nm, value := value, linked_to := lt, opened := ev.id } : Fact)] = 0 := by
          simp [hn]
        rw [hnew, Nat.add_zero]
        refine le_trans ?_ hold
        cases wide
        · simp only [Bool.false_eq_true, if_false, world.drop_slot] at hvf
          rw [drop_slot_ok hvf]; exact countP_filter_le _ _ _
        · simp only [if_true, world.drop_name] at hvf
          rw [drop_name_ok hvf]; exact countP_filter_le _ _ _
  case FactUpdate who nm lt fr tv =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact ot_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨o1, ho1, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply ot_insert (ot_erase h _)
      intro n hs
      -- The update keeps the name of every fact, so every count stays.
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
            simpa [alloc.vec.Vec.deref] using hlt i rfl
          simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize] at hvf
          simp [hi] at hvf
          subst hvf
          simp [List.map_set]
          have : (row.facts.val)[i.val].name =
              (row.facts.val.map (fun f : Fact => f.name))[i.val]'(by simpa using hi) := by simp
          rw [this, List.set_getElem_self]
      have hc : countName { row with facts := vf } n = countName row n := by
        simp only [countName]
        have := congrArg (List.countP (fun s : String => decide (s = n))) hnames
        simpa [List.countP_map, Function.comp_def] using this
      simpa [hc] using h _ _ n hr hs
  case FactEnd who nm lt =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    cases hr : (m : Std.ExtTreeMap Nat Entity compare)[who.val]? with
    | none => simp [hr] at ha; subst ha; exact ot_erase h _
    | some row =>
      simp [hr, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      apply ot_insert (ot_erase h _)
      intro n hs
      simp only [countName, drop_slot_ok hvf]
      exact le_trans (countP_filter_le _ _ _) (h _ _ n hr hs)

theorem reach_one_target {w u : World} (hr : Reach w u)
    (h : oneTarget w.vocabulary w.entities) : oneTarget u.vocabulary u.entities := by
  induction hr with
  | refl => exact h
  | @step u u' t k id _ hc ih =>
    obtain ⟨_, _, hv⟩ := commit_ok hc
    rw [hv]
    exact apply_one_target _ _ _ _ ih (commit_apply hc)

/-- ONE TARGET AT A TIME, IN EVERY WORLD. In a world that commits and
    proposals build from an empty world, a name that allows one target
    at a time holds at most one fact on each entity. For example, an
    entity sits in one place at a time. -/
theorem every_world_one_target (v : FactVocabulary) (w0 w : World)
    (h0 : World.new v = ok w0) (hr : Reach w0 w) : oneTarget w.vocabulary w.entities := by
  apply reach_one_target hr
  simp only [World.new, ids.Ids.new, EventHistory.new, bind_tc_ok, ok.injEq] at h0
  subst h0
  intro k e n hk
  simp at hk

end hourglass
