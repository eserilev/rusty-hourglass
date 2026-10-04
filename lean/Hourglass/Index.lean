-- The rung 11 laws: the creation event and the name index.
--
-- Each entity stores the event that created it, and the world keeps
-- the ids of each name. A caller reads both with no walk over the
-- history or the world. The laws below say that both agree with the
-- entities in every world that commits build.
import Hourglass.Referee

open Aeneas Aeneas.Std Result

namespace hourglass

open world event fact entity

/-! ## What `apply` does to a creation -/

/-- A creation of a new id inserts the new row. -/
theorem apply_creation {m m' : ids.Ids Entity} {v : FactVocabulary} {ev : Event}
    {id : time.EntityId} {ty : EntityType} {nm : String}
    (hkd : ev.kind = .EntityCreated id ty nm)
    (hnew : (m : Std.ExtTreeMap Nat Entity compare)[id.val]? = none)
    (ha : World.apply m v ev = ok m') :
    (m' : Std.ExtTreeMap Nat Entity compare)[id.val]? =
      some { id := id, entity_type := ty, «name» := nm,
             existence := { «from» := ev.tick, «until» := none },
             created := ev.id, facts := alloc.vec.Vec.new Fact } := by
  unfold World.apply at ha
  rw [hkd] at ha
  simp only [ids.Ids.contains, bind_tc_ok] at ha
  have hc : Std.ExtTreeMap.contains m id.val = false := by
    rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, hnew]; rfl
  simp only [hc, Bool.false_eq_true, if_false, alloc.string.String.Insts.CoreCloneClone.clone,
    time.TimeSpan.open, ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
  subst ha
  simp

/-- After `apply`, a key holds a row of a name exactly when it held one
    before, or when this event creates it with that name. -/
theorem apply_rows {m m' : ids.Ids Entity} {v : FactVocabulary} {ev : Event}
    (ha : World.apply m v ev = ok m') (j : Nat) (n : String) :
    (∃ e', (m' : Std.ExtTreeMap Nat Entity compare)[j]? = some e' ∧ e'.name = n) ↔
      (∃ e, (m : Std.ExtTreeMap Nat Entity compare)[j]? = some e ∧ e.name = n) ∨
      (∃ id ty, ev.kind = .EntityCreated id ty n ∧ id.val = j ∧
        (m : Std.ExtTreeMap Nat Entity compare)[j]? = none) := by
  constructor
  · rintro ⟨e', he', hn⟩
    rcases apply_shape m v ev m' ha j e' he' with
      ⟨e, he, _, _, hname, _⟩ | ⟨hnone, id, ty, nm, hid, hkd, rfl⟩
    · exact Or.inl ⟨e, he, by rw [← hname, hn]⟩
    · exact Or.inr ⟨id, ty, by rw [hkd, ← hn], hid, hnone⟩
  · rintro (⟨e, he, hn⟩ | ⟨id, ty, hkd, hid, hnone⟩)
    · have hk : holds m j := by
        unfold holds; rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, he]; rfl
      have hk' := apply_keeps_ids m v ev m' ha j hk
      unfold holds at hk'
      rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hk'
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hk'
      refine ⟨e', he', ?_⟩
      rcases apply_shape m v ev m' ha j e' he' with
        ⟨e0, he0, _, _, hname, _⟩ | ⟨hnone, _⟩
      · rw [he] at he0
        simp only [Option.some.injEq] at he0
        subst he0
        rw [hname, hn]
      · rw [he] at hnone; cases hnone
    · subst hid
      exact ⟨_, apply_creation hkd hnone ha, rfl⟩

/-! ## Invariant: every entity points at its creation -/

/-- Every entity points at the event that created it: the event at
    that place of the history carries that id, and it creates the
    entity with its id, its type, and its name. -/
def createdAt (m : ids.Ids Entity) (hist : List Event) : Prop :=
  ∀ (k : Nat) (e : Entity), (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e →
    ∃ t, hist[e.created.val]? = some ⟨e.created, t, .EntityCreated e.id e.entity_type e.name⟩

theorem apply_createdAt {m m' : ids.Ids Entity} {v : FactVocabulary} {ev : Event}
    {hist : List Event} (h : createdAt m hist) (hid : ev.id.val = hist.length)
    (ha : World.apply m v ev = ok m') : createdAt m' (hist ++ [ev]) := by
  intro k e' hk'
  rcases apply_shape m v ev m' ha k e' hk' with
    ⟨e, he, hsame, hty, hname, hcr, _⟩ | ⟨_, id, ty, nm, _, hkd, rfl⟩
  · obtain ⟨t, ht⟩ := h k e he
    have hlt : e.created.val < hist.length := (List.getElem?_eq_some_iff.1 ht).1
    refine ⟨t, ?_⟩
    rw [hcr, hsame, hty, hname, List.getElem?_append_left hlt]
    exact ht
  · refine ⟨ev.tick, ?_⟩
    rw [List.getElem?_append_right (by simp [hid])]
    simp only [hid, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq]
    cases ev
    simp only at hkd
    rw [hkd]

theorem reach_createdAt {w u : World} (hr : Reach w u)
    (h : createdAt w.entities w.history.val) : createdAt u.entities u.history.val := by
  induction hr with
  | refl => exact h
  | step _ hc ih =>
    obtain ⟨hid, hhist, _⟩ := commit_facts hc
    rw [hhist]
    exact apply_createdAt ih hid (commit_apply hc)

/-- THE CREATION EVENT IS STORED. In every world that commits and
    proposals build from an empty world, each entity points at the
    event of the history that created it, with its id, type, and
    name. So a caller finds that event with no walk over the
    history. -/
theorem every_world_created (v : FactVocabulary) (w0 w : World)
    (h0 : World.new v = ok w0) (hr : Reach w0 w) :
    createdAt w.entities w.history.val := by
  apply reach_createdAt hr
  simp only [World.new, ids.Ids.new, names.Names.new, EventHistory.new, bind_tc_ok,
    ok.injEq] at h0
  subst h0
  intro k e hk
  simp at hk

/-! ## Invariant: the name index agrees with the entities -/

/-- The ids under one name of the index. -/
def namedIds (nx : names.Names (alloc.vec.Vec time.EntityId)) (n : String) :
    List time.EntityId :=
  match (nx : Std.ExtTreeMap String (alloc.vec.Vec time.EntityId) compare)[n]? with
  | some l => l.val
  | none => []

/-- The index holds each id of a name one time, and it holds exactly
    the entities of that name. -/
def namedOk (nx : names.Names (alloc.vec.Vec time.EntityId)) (m : ids.Ids Entity) : Prop :=
  (∀ n, (namedIds nx n).Nodup) ∧
  ∀ n (i : time.EntityId), i ∈ namedIds nx n ↔
    ∃ e, (m : Std.ExtTreeMap Nat Entity compare)[i.val]? = some e ∧ e.name = n

/-- A creation of a new id adds the id at the end of its name. -/
theorem index_new {nx nx' : names.Names (alloc.vec.Vec time.EntityId)} {m : ids.Ids Entity}
    {ev : Event} {id : time.EntityId} {ty : EntityType} {nm : String}
    (hkd : ev.kind = .EntityCreated id ty nm)
    (hnew : (m : Std.ExtTreeMap Nat Entity compare)[id.val]? = none)
    (hx : World.index nx m ev = ok nx') (n : String) :
    namedIds nx' n = if n = nm then namedIds nx nm ++ [id] else namedIds nx n := by
  unfold World.index at hx
  rw [hkd] at hx
  have hc : Std.ExtTreeMap.contains m id.val = false := by
    rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, hnew]; rfl
  simp only [ids.Ids.contains, hc, bind_tc_ok, Bool.false_eq_true, if_false,
    names.Names.take_key, alloc.string.String.Insts.CoreCloneClone.clone] at hx
  obtain ⟨l1, hp, hx⟩ : ∃ l1, alloc.vec.Vec.push
      (match (nx : Std.ExtTreeMap String (alloc.vec.Vec time.EntityId) compare)[nm]? with
        | none => alloc.vec.Vec.new time.EntityId
        | some l => l) id = ok l1 ∧
      nx' = Std.ExtTreeMap.insert (Std.ExtTreeMap.erase nx nm) nm l1 := by
    cases hg : (nx : Std.ExtTreeMap String (alloc.vec.Vec time.EntityId) compare)[nm]? <;>
      simp [hg] at hx <;>
      rw [bind_eq_ok] at hx <;> obtain ⟨l1, hp, hx⟩ := hx <;>
      simp only [names.Names.insert, ok.injEq] at hx <;> exact ⟨l1, hp, hx.symm⟩
  have hold : (match (nx : Std.ExtTreeMap String (alloc.vec.Vec time.EntityId) compare)[nm]? with
      | none => alloc.vec.Vec.new time.EntityId
      | some l => l).val = namedIds nx nm := by
    unfold namedIds
    cases (nx : Std.ExtTreeMap String (alloc.vec.Vec time.EntityId) compare)[nm]? <;>
      simp [alloc.vec.Vec.new]
  subst hx
  unfold namedIds
  by_cases hn : n = nm
  · subst hn
    simp [push_val_any hp, hold, namedIds]
  · simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase, hn, Ne.symm hn]

/-- Any other event leaves the index as it was. -/
theorem index_same {nx nx' : names.Names (alloc.vec.Vec time.EntityId)} {m : ids.Ids Entity}
    {ev : Event}
    (hnot : ∀ id ty nm, ev.kind = .EntityCreated id ty nm →
      (m : Std.ExtTreeMap Nat Entity compare)[id.val]? ≠ none)
    (hx : World.index nx m ev = ok nx') : nx' = nx := by
  unfold World.index at hx
  cases hkd : ev.kind <;> simp only [hkd, ok.injEq] at hx
  case EntityCreated id ty nm =>
    have hc : Std.ExtTreeMap.contains m id.val = true := by
      rw [Std.ExtTreeMap.contains_eq_isSome_getElem?]
      cases h : (m : Std.ExtTreeMap Nat Entity compare)[id.val]? with
      | none => exact absurd h (hnot id ty nm hkd)
      | some _ => rfl
    simp only [ids.Ids.contains, hc, bind_tc_ok, if_true, ok.injEq] at hx
    exact hx.symm
  all_goals exact hx.symm

theorem u32_ext {a b : time.EntityId} (h : a.val = b.val) : a = b := by
  scalar_tac

theorem index_step {nx nx' : names.Names (alloc.vec.Vec time.EntityId)}
    {m m' : ids.Ids Entity} {v : FactVocabulary} {ev : Event}
    (h : namedOk nx m) (hx : World.index nx m ev = ok nx')
    (ha : World.apply m v ev = ok m') : namedOk nx' m' := by
  obtain ⟨hnd, hmem⟩ := h
  by_cases hc : ∃ id ty nm, ev.kind = .EntityCreated id ty nm ∧
      (m : Std.ExtTreeMap Nat Entity compare)[id.val]? = none
  · obtain ⟨id, ty, nm, hkd, hnew⟩ := hc
    have hidx := index_new hkd hnew hx
    -- The new id is under no name yet.
    have hfresh : ∀ n, id ∉ namedIds nx n := by
      intro n hin
      obtain ⟨e, he, _⟩ := (hmem n id).1 hin
      rw [hnew] at he; cases he
    refine ⟨fun n => ?_, fun n i => ?_⟩
    · rw [hidx n]
      split
      · refine List.nodup_append.2 ⟨hnd nm, List.nodup_singleton _, ?_⟩
        intro a ha b hb hab
        simp only [List.mem_singleton] at hb
        subst hb hab
        exact hfresh nm ha
      · exact hnd n
    · rw [hidx n, apply_rows ha, ← hmem n i]
      split
      · rename_i hn
        subst hn
        rw [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h1 | rfl)
          · exact Or.inl h1
          · exact Or.inr ⟨i, ty, hkd, rfl, hnew⟩
        · rintro (h1 | ⟨id', ty', hk', hid', _⟩)
          · exact Or.inl h1
          · right
            rw [hkd] at hk'
            simp only [EventKind.EntityCreated.injEq] at hk'
            obtain ⟨rfl, _, _⟩ := hk'
            exact u32_ext hid'.symm
      · rename_i hn
        constructor
        · exact Or.inl
        · rintro (h1 | ⟨id', ty', hk', _, _⟩)
          · exact h1
          · rw [hkd] at hk'
            simp only [EventKind.EntityCreated.injEq] at hk'
            exact absurd hk'.2.2.symm hn
  · have hnot : ∀ id ty nm, ev.kind = .EntityCreated id ty nm →
        (m : Std.ExtTreeMap Nat Entity compare)[id.val]? ≠ none :=
      fun id ty nm hk hn => hc ⟨id, ty, nm, hk, hn⟩
    rw [index_same hnot hx]
    refine ⟨hnd, fun n i => ?_⟩
    rw [apply_rows ha, ← hmem n i]
    constructor
    · exact Or.inl
    · rintro (h1 | ⟨id', ty', hk', hid', hn'⟩)
      · exact h1
      · exact absurd (by rw [hid']; exact hn') (hnot id' ty' n hk')

/-- A commit that succeeds passed its index through `index`. -/
theorem commit_index {w w' : World} {t : time.Tick} {k : EventKind} {id : time.EventId}
    (hc : World.commit w t k = ok (id, w')) :
    World.index w.named w.entities ⟨id, t, k⟩ = ok w'.named := by
  unfold World.commit at hc
  cases hn : EventHistory.next_id w.history
  case ret id0 =>
    simp only [hn, bind_tc_ok] at hc
    cases hx : World.index w.named w.entities ⟨id0, t, k⟩
    case ret nm =>
      simp only [hx, bind_tc_ok] at hc
      cases ha : World.apply w.entities w.vocabulary ⟨id0, t, k⟩
      case ret bm =>
        simp only [ha, bind_tc_ok, EventHistory.append] at hc
        cases hp : alloc.vec.Vec.push w.history ⟨id0, t, k⟩
        case ret eh =>
          simp only [hp, bind_tc_ok, time.Tick.Insts.CoreCmpPartialOrdTick.gt] at hc
          split at hc <;> simp only [ok.injEq, Prod.mk.injEq] at hc <;>
            obtain ⟨rfl, rfl⟩ := hc <;> exact hx
        all_goals simp [hp] at hc
      all_goals simp [ha] at hc
    all_goals simp [hx] at hc
  all_goals simp [hn] at hc

theorem reach_named {w u : World} (hr : Reach w u)
    (h : namedOk w.named w.entities) : namedOk u.named u.entities := by
  induction hr with
  | refl => exact h
  | step _ hc ih => exact index_step ih (commit_index hc) (commit_apply hc)

/-- THE NAME INDEX AGREES WITH THE ENTITIES. In every world that
    commits and proposals build from an empty world, the index holds
    each id of a name one time, and an id sits under a name exactly
    when the world holds an entity of that id and that name. So a
    caller finds an entity by its name with no walk over the world. -/
theorem every_world_named (v : FactVocabulary) (w0 w : World)
    (h0 : World.new v = ok w0) (hr : Reach w0 w) : namedOk w.named w.entities := by
  apply reach_named hr
  simp only [World.new, ids.Ids.new, names.Names.new, EventHistory.new, bind_tc_ok,
    ok.injEq] at h0
  subst h0
  refine ⟨fun n => by simp [namedIds], fun n i => ?_⟩
  simp [namedIds]

end hourglass
