-- The rung 5 direction law: an `Up` fact never falls and never ends,
-- in every world that proposals build.
import Hourglass.Gate

open Aeneas Aeneas.Std Result

namespace hourglass

open world event fact entity

/-! ## Pure mirrors of the direction -/

def dirOf : Shape → Direction
  | .Flag d => d
  | .Number _ d => d

@[simp] theorem direction_eq (s : Shape) : s.direction = ok (dirOf s) := by
  cases s <;> simp [Shape.direction, dirOf]

def allowsB : Direction → Std.I64 → Std.I64 → Bool
  | .Up, a, b => decide (b >= a)
  | .Down, a, b => decide (b <= a)
  | .Free, _, _ => true

@[simp] theorem allows_eq (d : Direction) (a b : Std.I64) : d.allows a b = ok (allowsB d a b) := by
  cases d <;> simp [Direction.allows, allowsB]

def canEndB : Direction → Bool
  | .Up => false
  | _ => true

@[simp] theorem can_end_eq (d : Direction) : d.can_end = ok (canEndB d) := by
  cases d <;> simp [Direction.can_end, canEndB]

/-! ## A refused holder leaves a fault -/

theorem live_holder_false {w : World} {who : time.EntityId} {o o1 : alloc.vec.Vec reject.Rejection}
    {b : Bool} (h : validate.live_holder w who o = ok (b, o1)) (hb : b = false) : o1.val ≠ [] := by
  unfold validate.live_holder at h
  rw [bind_eq_ok] at h
  obtain ⟨ent, _, h⟩ := h
  cases ent with
  | none =>
    rw [bind_eq_ok] at h
    obtain ⟨o2, hp, h⟩ := h
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact push_ne hp
  | some row =>
    rw [bind_eq_ok] at h
    obtain ⟨g, _, h⟩ := h
    split at h
    · rw [bind_eq_ok] at h
      obtain ⟨o2, hp, h⟩ := h
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact push_ne hp
    · simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp at hb

/-! ## What a clean gate says about the direction -/

@[simp] theorem option_ne_i64 (a b : Option Std.I64) :
    core.option.Option.Insts.CoreCmpPartialEqOption.ne core.cmp.PartialEqI64 a b =
      ok (decide (a ≠ b)) := by
  cases a <;> cases b <;>
    simp [core.option.Option.Insts.CoreCmpPartialEqOption.ne,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq]
  constructor <;> intro h <;> scalar_tac


/-- A START WITH NO FAULT does not go back from the value it meets. -/
theorem start_dir {w : World} {who : time.EntityId} {nm : String} {v : Option Std.I64}
    {lt : Option time.EntityId} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.start w who nm v lt o = ok o') (he : o'.val = [])
    (r : FactRules) (hr : (w.vocabulary.names : names.Names FactRules)[nm]? = some r)
    (was now : Std.I64) (hh : validate.held_for_start w who nm lt = ok (some (some was)))
    (hv : v = some now) : allowsB (dirOf (shapeOf r)) was now = true := by
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
  have hr2 : out2.val <+: out2.val := List.prefix_refl _
  have p3 : out2.val <+: out3.val := grows_of (by grows) h3
  have p2 : out1.val <+: out2.val := grows_of (number_fits_grows _ _ _ _) h2
  have e4 := nil_of_prefix_nil p5 he
  have e1 := nil_of_prefix_nil (p2.trans (p3.trans p4)) e4
  -- The holder is alive, or the gate left a fault.
  have hholder : holder = true := by
    cases holder
    · exact absurd e1 (live_holder_false h1 rfl)
    · rfl
  subst hholder
  simp only [if_true, hh, bind_tc_ok, hv] at h
  split at h
  · assumption
  · exact absurd he (by
      rw [bind_eq_ok] at h
      obtain ⟨_, _, h⟩ := h
      exact push_ne h)

/-- AN UPDATE WITH NO FAULT replaces the value the world holds, and it
    does not go back from it. -/
theorem update_dir {w : World} {who : time.EntityId} {nm : String}
    {lt : Option time.EntityId} {fr tv : Std.I64} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.update w who nm lt fr tv o = ok o') (he : o'.val = [])
    (r : FactRules) (hr : (w.vocabulary.names : names.Names FactRules)[nm]? = some r) :
    (∀ held, validate.slot_value w who nm lt = ok (some held) → held = some fr) ∧
    (∀ band d, shapeOf r = .Number band d → allowsB d fr tv = true) := by
  unfold validate.update at h
  rw [bind_eq_ok] at h
  obtain ⟨⟨holder, out1⟩, h1, h⟩ := h
  simp only [FactVocabulary.rules_key, names.Names.get_key] at h
  simp [hr] at h
  rw [bind_eq_ok] at h
  obtain ⟨out2, h2, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out3, h3, h⟩ := h
  have hr2 : out2.val <+: out2.val := List.prefix_refl _
  have p3 : out2.val <+: out3.val := grows_of (by grows) h3
  have hr3 : out3.val <+: out3.val := List.prefix_refl _
  have p4 : out3.val <+: o'.val := grows_of (by grows) h
  have e3 := nil_of_prefix_nil p4 he
  have e2 := nil_of_prefix_nil p3 e3
  have hr1 : out1.val <+: out1.val := List.prefix_refl _
  have p2 : out1.val <+: out2.val := grows_of (by grows) h2
  have e1 := nil_of_prefix_nil p2 e2
  refine ⟨?_, ?_⟩
  · intro held hs
    have hholder : holder = true := by
      cases holder
      · exact absurd e1 (live_holder_false h1 rfl)
      · rfl
    subst hholder
    simp only [if_true, hs, bind_tc_ok, lift] at h
    split at h
    · assumption
    · rw [bind_eq_ok] at h
      obtain ⟨_, _, h⟩ := h
      exact absurd he (push_ne h)
  · intro band d hs
    rw [hs] at h2
    simp at h2
    rw [bind_eq_ok] at h2
    obtain ⟨out3', h3', h2⟩ := h2
    split at h2
    · assumption
    · rw [bind_eq_ok] at h2
      obtain ⟨_, _, h2⟩ := h2
      exact absurd e2 (push_ne h2)

/-- AN END WITH NO FAULT ends a fact whose direction allows an end. -/
theorem end_dir {w : World} {who : time.EntityId} {nm : String}
    {lt : Option time.EntityId} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.end w who nm lt o = ok o') (he : o'.val = [])
    (r : FactRules) (hr : (w.vocabulary.names : names.Names FactRules)[nm]? = some r) :
    canEndB (dirOf (shapeOf r)) = true := by
  unfold validate.end at h
  simp only [FactVocabulary.rules_key, names.Names.get_key] at h
  simp [hr] at h
  rw [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out1, _, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out2, h2, h⟩ := h
  have hr2 : out2.val <+: out2.val := List.prefix_refl _
  have p : out2.val <+: o'.val := grows_of (by grows) h
  have e2 := nil_of_prefix_nil p he
  split at h2
  · assumption
  · rw [bind_eq_ok] at h2
    obtain ⟨_, _, h2⟩ := h2
    exact absurd e2 (push_ne h2)

/-- What a clean gate says about the direction of an event. -/
def dirClean (w : World) : EventKind → Prop
  | .FactStart who nm value lt =>
    ∀ r, (w.vocabulary.names : names.Names FactRules)[nm]? = some r →
      ∀ was now, validate.held_for_start w who nm lt = ok (some (some was)) → value = some now →
        allowsB (dirOf (shapeOf r)) was now = true
  | .FactUpdate who nm lt fr tv =>
    ∀ r, (w.vocabulary.names : names.Names FactRules)[nm]? = some r →
      (∀ held, validate.slot_value w who nm lt = ok (some held) → held = some fr) ∧
      (∀ band d, shapeOf r = .Number band d → allowsB d fr tv = true)
  | .FactEnd _ nm _ =>
    ∀ r, (w.vocabulary.names : names.Names FactRules)[nm]? = some r →
      canEndB (dirOf (shapeOf r)) = true
  | _ => True

/-- A GATE WITH NO FAULT passes only an event that keeps the direction. -/
theorem validate_dir {w : World} {t : time.Tick} {k : EventKind}
    {f : alloc.vec.Vec reject.Rejection}
    (h : validate.validate w t k = ok f) (he : f.val = []) : dirClean w k := by
  unfold validate.validate at h
  rw [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out, _, h⟩ := h
  cases k with
  | FactStart who nm value lt => exact fun r hr was now hh hv => start_dir h he r hr was now hh hv
  | FactUpdate who nm lt fr tv => exact fun r hr => update_dir h he r hr
  | FactEnd who nm lt => exact fun r hr => end_dir h he r hr
  | _ => trivial

/-! ## The slot queries, on a world with one fact per slot -/

theorem slot_unique {facts : List Fact} (hn : (facts.map slotOf).Nodup) {x y : Fact}
    (hx : x ∈ facts) (hy : y ∈ facts) (hxy : slotOf x = slotOf y) : x = y :=
  List.inj_on_of_nodup_map hn hx hy hxy

theorem inSlot_iff (x : Fact) (n : String) (l : Option time.EntityId) :
    inSlot x n l = true ↔ slotOf x = (n, l) := by
  simp [inSlot]

/-- On a list with one fact per slot, the slot search finds the fact in
    the slot. -/
theorem slot_index_finds {facts : alloc.vec.Vec Fact} (hn : (facts.val.map slotOf).Nodup)
    {x : Fact} (hx : x ∈ facts.val) {n : String} {l : Option time.EntityId}
    (hs : inSlot x n l = true) :
    ∃ i, world.slot_index facts.deref n l = ok (some i) ∧
      ∃ hi : i.val < facts.val.length, facts.val[i.val] = x := by
  obtain ⟨o, ho, post⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
    (slot_index_spec facts.deref n l)
  cases o with
  | none =>
    have := post.2 rfl x (by simpa [alloc.vec.Vec.deref] using hx)
    rw [hs] at this; exact absurd this (by simp)
  | some i =>
    obtain ⟨hj, hin⟩ := post.1 i rfl
    have hi : i.val < facts.val.length := by simpa [alloc.vec.Vec.deref] using hj
    refine ⟨i, ho, hi, ?_⟩
    apply slot_unique hn (List.getElem_mem hi) hx
    rw [(inSlot_iff _ _ _).1 (by simpa [alloc.vec.Vec.deref] using hin),
      (inSlot_iff _ _ _).1 hs]

theorem entity_eq (w : World) (id : time.EntityId) :
    World.entity w id = ok ((w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]?) := by
  simp [World.entity, ids.Ids.get]

theorem slot_value_eq (w : World) (k : time.EntityId) (e : Entity)
    (he : (w.entities : Std.ExtTreeMap Nat Entity compare)[k.val]? = some e)
    (hn : (slots e).Nodup) (x : Fact) (hx : x ∈ e.facts.val) (n : String)
    (l : Option time.EntityId) (hs : inSlot x n l = true) :
    validate.slot_value w k n l = ok (some x.value) := by
  obtain ⟨i, hi, hlt, hxi⟩ := slot_index_finds hn hx hs
  unfold validate.slot_value
  simp [entity_eq, he, hi, alloc.vec.Vec.index_usize, hlt, hxi]

theorem held_for_start_eq (w : World) (k : time.EntityId) (e : Entity)
    (he : (w.entities : Std.ExtTreeMap Nat Entity compare)[k.val]? = some e)
    (hn : (slots e).Nodup) (x : Fact) (hx : x ∈ e.facts.val) (n : String)
    (l : Option time.EntityId) (hs : inSlot x n l = true)
    (hsingle : world.single_target w.vocabulary n = ok false) :
    validate.held_for_start w k n l = ok (some x.value) := by
  obtain ⟨i, hi, hlt, hxi⟩ := slot_index_finds hn hx hs
  unfold validate.held_for_start
  simp [entity_eq, he, hsingle, hi, alloc.vec.Vec.index_usize, hlt, hxi]

/-! ## One step: an `Up` fact never falls and never ends -/

/-- The entity `k` holds a fact in the slot of `n` and `l`, with value `a`. -/
def upHeld (m : ids.Ids Entity) (k : Nat) (n : String) (l : Option time.EntityId)
    (a : Option Std.I64) : Prop :=
  ∃ e, (m : Std.ExtTreeMap Nat Entity compare)[k]? = some e ∧
    ∃ x ∈ e.facts.val, inSlot x n l = true ∧ x.value = a

/-- A value that did not go back: a flag stays a flag, and a number
    does not fall. -/
def upLe : Option Std.I64 → Option Std.I64 → Prop
  | none, none => True
  | some x, some y => x.val ≤ y.val
  | _, _ => False

theorem upLe_refl (a : Option Std.I64) : upLe a a := by
  cases a <;> simp [upLe]

theorem upLe_trans {a b c : Option Std.I64} (h1 : upLe a b) (h2 : upLe b c) : upLe a c := by
  cases a <;> cases b <;> cases c <;> simp_all [upLe]
  omega

/-- A name whose direction is `Up`, and that allows more than one
    target (or takes none). -/
def upName (v : FactVocabulary) (n : String) : Prop :=
  ∃ r, (v.names : names.Names FactRules)[n]? = some r ∧ dirOf (shapeOf r) = .Up ∧
    world.single_target v n = ok false

theorem upHeld_same {m m' : ids.Ids Entity} {k : Nat} {n : String} {l : Option time.EntityId}
    {a : Option Std.I64}
    (hget : (m' : Std.ExtTreeMap Nat Entity compare)[k]? = (m : Std.ExtTreeMap Nat Entity compare)[k]?)
    (h : upHeld m k n l a) : ∃ b, upHeld m' k n l b ∧ upLe a b := by
  obtain ⟨e, hk, x, hx, hs, hxa⟩ := h
  exact ⟨a, ⟨e, hget.trans hk, x, hx, hs, hxa⟩, upLe_refl a⟩

theorem get_insert_erase_ne (m : ids.Ids Entity) (j k : Nat) (row : Entity) (hjk : j ≠ k) :
    (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m j) j row : Std.ExtTreeMap Nat Entity compare)[k]? =
      (m : Std.ExtTreeMap Nat Entity compare)[k]? := by
  rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase]
  simp [hjk]

theorem get_insert_erase_eq (m : ids.Ids Entity) (k : Nat) (row : Entity) :
    (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k row : Std.ExtTreeMap Nat Entity compare)[k]? =
      some row := by
  simp

theorem get_erase_ne (m : ids.Ids Entity) (j k : Nat) (hjk : j ≠ k) :
    (Std.ExtTreeMap.erase m j : Std.ExtTreeMap Nat Entity compare)[k]? =
      (m : Std.ExtTreeMap Nat Entity compare)[k]? := by
  rw [Std.ExtTreeMap.getElem?_erase]
  simp [hjk]

theorem mem_set_ne {lst : List Fact} {i : Nat} {x y : Fact} (hx : x ∈ lst)
    (hne : ∀ h : i < lst.length, lst[i] ≠ x) : x ∈ lst.set i y := by
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
  have hji : j ≠ i := by
    intro h; subst h; exact hne hj hjx
  rw [List.mem_iff_getElem]
  refine ⟨j, by simpa using hj, ?_⟩
  rw [List.getElem_set]
  simp [Ne.symm hji, hjx]

/-- ONE STEP. A clean event that `apply` folds in never lowers and never
    ends a fact of an `Up` name. -/
theorem apply_up (w : World) (ev : Event) (m' : ids.Ids Entity)
    (hslots : oneFactPerSlot w.entities) (hband : inBand w.vocabulary w.entities)
    (hc : cleanKind w.vocabulary ev.kind) (hd : dirClean w ev.kind)
    (ha : World.apply w.entities w.vocabulary ev = ok m')
    (n : String) (l : Option time.EntityId) (hu : upName w.vocabulary n)
    (k : Nat) (a : Option Std.I64) (hh : upHeld w.entities k n l a) :
    ∃ b, upHeld m' k n l b ∧ upLe a b := by
  obtain ⟨r, hr, hup, hsingle⟩ := hu
  obtain ⟨e, hke, x, hx, hs, hxa⟩ := hh
  have hh : upHeld w.entities k n l a := ⟨e, hke, x, hx, hs, hxa⟩
  have hslot : slotOf x = (n, l) := (inSlot_iff _ _ _).1 hs
  unfold World.apply at ha
  cases hk : ev.kind <;> simp only [hk] at ha <;> rw [hk] at hc hd
  case EntityCreated id ty nm =>
    simp only [ids.Ids.contains, bind_tc_ok] at ha
    split at ha
    · simp only [ok.injEq] at ha; subst ha; exact upHeld_same rfl hh
    · rename_i hnot
      simp only [alloc.string.String.Insts.CoreCloneClone.clone, time.TimeSpan.open,
        ids.Ids.insert, bind_tc_ok, ok.injEq] at ha
      subst ha
      have hne : id.val ≠ k := by
        intro heq; subst heq
        apply hnot
        simp [Std.ExtTreeMap.contains_eq_isSome_getElem?, hke]
      apply upHeld_same _ hh
      rw [Std.ExtTreeMap.getElem?_insert]
      simp [hne]
  case EntityDestroyed id =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    by_cases hid : id.val = k
    · subst hid
      simp [hke, ids.Ids.insert] at ha
      split at ha
      all_goals
        simp only [bind_tc_ok, ok.injEq] at ha
        subst ha
        exact ⟨a, ⟨_, get_insert_erase_eq _ _ _, x, hx, hs, hxa⟩, upLe_refl a⟩
    · cases hr' : (w.entities : Std.ExtTreeMap Nat Entity compare)[id.val]? with
      | none =>
        simp [hr'] at ha; subst ha
        exact upHeld_same (get_erase_ne _ _ _ hid) hh
      | some row =>
        simp [hr', ids.Ids.insert] at ha
        split at ha
        all_goals
          simp only [bind_tc_ok, ok.injEq] at ha
          subst ha
          exact upHeld_same (get_insert_erase_ne _ _ _ _ hid) hh
  case FactEnd who nm lt =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    by_cases hwk : who.val = k
    · subst hwk
      simp [hke, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      refine ⟨a, ⟨_, get_insert_erase_eq _ _ _, x, ?_, hs, hxa⟩, upLe_refl a⟩
      rw [drop_slot_ok hvf, List.mem_filter]
      refine ⟨hx, ?_⟩
      -- The end names another slot: an `Up` fact never ends.
      by_cases hsl : slotOf x = (nm, lt)
      · rw [hslot] at hsl
        simp only [Prod.mk.injEq] at hsl
        obtain ⟨rfl, rfl⟩ := hsl
        have := hd r hr
        rw [hup] at this
        simp [canEndB] at this
      · simp only [inSlot, hsl, decide_false, Bool.not_false]
    · cases hr' : (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? with
      | none =>
        simp [hr'] at ha; subst ha
        exact upHeld_same (get_erase_ne _ _ _ hwk) hh
      | some row =>
        simp [hr', ids.Ids.insert] at ha
        rw [bind_eq_ok] at ha
        obtain ⟨_, _, ha⟩ := ha
        simp only [ok.injEq] at ha
        subst ha
        exact upHeld_same (get_insert_erase_ne _ _ _ _ hwk) hh
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨wide, hwide, ha⟩ := ha
    simp only [ids.Ids.take, bind_tc_ok] at ha
    by_cases hwk : who.val = k
    · subst hwk
      simp [hke, ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨v1, hv1, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      have hv1val := push_val_any hv1
      -- The fact stays, when the event names another slot.
      have stays : x ∈ vf.val → ∃ b, upHeld (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase w.entities
          who.val) who.val { e with facts := v1 }) who.val n l b ∧ upLe a b := by
        intro hxv
        exact ⟨a, ⟨_, get_insert_erase_eq _ _ _, x, by rw [hv1val]; simp [hxv], hs, hxa⟩,
          upLe_refl a⟩
      cases wide
      · simp only [Bool.false_eq_true, if_false, world.drop_slot] at hvf
        by_cases hsl : slotOf x = (nm, lt)
        · -- The event names the slot of the fact: the new fact takes it.
          rw [hslot] at hsl
          simp only [Prod.mk.injEq] at hsl
          obtain ⟨rfl, rfl⟩ := hsl
          have hheld := held_for_start_eq w who e hke (hslots _ _ hke) x hx n l hs hsingle
          obtain ⟨r0, hr0, hnum0⟩ := hband _ _ x hke hx
          have hxn : x.name = n := by
            have := congrArg Prod.fst hslot; simpa [slotOf] using this
          rw [hxn, hr] at hr0
          simp only [Option.some.injEq] at hr0
          subst hr0
          obtain ⟨r1, hr1, hnum1⟩ := hc
          rw [hr] at hr1
          simp only [Option.some.injEq] at hr1
          subst hr1
          refine ⟨value, ⟨_, get_insert_erase_eq _ _ _,
            ({ «name» := n, value := value, linked_to := l, opened := ev.id } : Fact),
            by rw [hv1val]; simp, ?_, rfl⟩, ?_⟩
          · simp [inSlot, slotOf]
          · rw [← hxa]
            cases hs0 : shapeOf r with
            | Flag d =>
              rw [hs0] at hnum0 hnum1
              simp only [numOk] at hnum0 hnum1
              rw [hnum0, hnum1]; trivial
            | Number band d =>
              rw [hs0] at hnum0 hnum1
              obtain ⟨was, hwas, _⟩ := hnum0
              obtain ⟨now, hnow, _⟩ := hnum1
              have hallow := hd r hr was now (by rw [hheld, hwas]) hnow
              rw [hup] at hallow
              rw [hwas, hnow]
              simp [upLe, allowsB] at hallow ⊢
              scalar_tac
        · apply stays
          rw [drop_slot_ok hvf, List.mem_filter]
          refine ⟨hx, ?_⟩
          simp only [inSlot, hsl, decide_false, Bool.not_false]
      · -- A single-target name: it is not the name of the fact.
        have hnm : nm ≠ n := by
          intro heq; subst heq
          rw [hsingle] at hwide
          simp at hwide
        simp only [if_true, world.drop_name] at hvf
        apply stays
        rw [drop_name_ok hvf, List.mem_filter]
        refine ⟨hx, ?_⟩
        have hxn : x.name = n := by
          have := congrArg Prod.fst hslot; simpa [slotOf] using this
        simp [hxn, Ne.symm hnm]
    · cases hr' : (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? with
      | none =>
        simp [hr'] at ha; subst ha
        exact upHeld_same (get_erase_ne _ _ _ hwk) hh
      | some row =>
        simp [hr', ids.Ids.insert, alloc.string.String.Insts.CoreCloneClone.clone] at ha
        repeat (rw [bind_eq_ok] at ha; obtain ⟨_, _, ha⟩ := ha)
        simp only [ok.injEq] at ha
        subst ha
        exact upHeld_same (get_insert_erase_ne _ _ _ _ hwk) hh
  case FactUpdate who nm lt fr tv =>
    simp only [ids.Ids.take, bind_tc_ok] at ha
    by_cases hwk : who.val = k
    · subst hwk
      simp [hke, ids.Ids.insert] at ha
      rw [bind_eq_ok] at ha
      obtain ⟨o1, ho1, ha⟩ := ha
      rw [bind_eq_ok] at ha
      obtain ⟨vf, hvf, ha⟩ := ha
      simp only [ok.injEq] at ha
      subst ha
      cases o1 with
      | none =>
        simp only [ok.injEq] at hvf
        subst hvf
        exact ⟨a, ⟨_, get_insert_erase_eq _ _ _, x, hx, hs, hxa⟩, upLe_refl a⟩
      | some i =>
        obtain ⟨_, ho1', hpost⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
          (slot_index_spec e.facts.deref nm lt)
        rw [ho1] at ho1'
        simp only [ok.injEq] at ho1'
        subst ho1'
        have hj := (hpost.1 i rfl).fst
        have hin := (hpost.1 i rfl).snd
        have hi : i.val < e.facts.val.length := by simpa [alloc.vec.Vec.deref] using hj
        have hin' : inSlot e.facts.val[i.val] nm lt = true := by
          simpa [alloc.vec.Vec.deref] using hin
        simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize] at hvf
        simp [hi] at hvf
        subst hvf
        by_cases hsl : slotOf x = (nm, lt)
        · -- The update names the slot of the fact.
          rw [hslot] at hsl
          simp only [Prod.mk.injEq] at hsl
          obtain ⟨rfl, rfl⟩ := hsl
          have hxi : e.facts.val[i.val] = x :=
            slot_unique (hslots _ _ hke) (List.getElem_mem hi) hx
              (by rw [(inSlot_iff _ _ _).1 hin', hslot])
          have hval := slot_value_eq w who e hke (hslots _ _ hke) x hx n l hs
          obtain ⟨r1, band, d, hr1, hs1, _⟩ := hc
          rw [hr] at hr1
          simp only [Option.some.injEq] at hr1
          subst hr1
          obtain ⟨hstale, hallow⟩ := hd r hr
          have hfr := hstale _ hval
          have hd' := hallow band d hs1
          have hdup : d = .Up := by rw [← hup, hs1]; rfl
          subst hdup
          refine ⟨some tv, ⟨_, get_insert_erase_eq _ _ _,
            ({ «name» := x.name, value := some tv, linked_to := x.linked_to, opened := ev.id } : Fact),
            ?_, ?_, rfl⟩, ?_⟩
          · simp [List.set_set]
            exact List.mem_iff_getElem.2 ⟨i.val, by simpa using hi, by simp [hxi]⟩
          · simpa [inSlot, slotOf] using hslot
          · rw [← hxa, hfr]
            simp [upLe, allowsB] at hd' ⊢
            scalar_tac
        · -- The update names another slot: the fact stays.
          refine ⟨a, ⟨_, get_insert_erase_eq _ _ _, x, ?_, hs, hxa⟩, upLe_refl a⟩
          simp only [alloc.vec.Vec.set_val_eq, List.set_set]
          apply mem_set_ne hx
          intro _ heq
          apply hsl
          rw [← heq]
          exact (inSlot_iff _ _ _).1 hin'
    · cases hr' : (w.entities : Std.ExtTreeMap Nat Entity compare)[who.val]? with
      | none =>
        simp [hr'] at ha; subst ha
        exact upHeld_same (get_erase_ne _ _ _ hwk) hh
      | some row =>
        simp [hr', ids.Ids.insert] at ha
        repeat (rw [bind_eq_ok] at ha; obtain ⟨_, _, ha⟩ := ha)
        simp only [ok.injEq] at ha
        subst ha
        exact upHeld_same (get_insert_erase_ne _ _ _ _ hwk) hh

/-! ## Every world that proposals build -/

theorem reachP_trans {a b c : World} (h1 : ReachP a b) (h2 : ReachP b c) : ReachP a c := by
  induction h2 with
  | refl => exact h1
  | step _ hp ih => exact ReachP.step ih hp

theorem reachP_vocab {a b : World} (h : ReachP a b) : b.vocabulary = a.vocabulary := by
  obtain ⟨_, _, _, hv⟩ := reach_history (reachP_reach h)
  exact hv

/-- AN `UP` FACT NEVER FALLS AND NEVER ENDS. In a world that proposals
    build from an empty world, a fact of an `Up` name stays in its slot
    in every later world, and its number never falls. For example, a
    best depth never falls, and an unlock is never lost. -/
theorem up_never_falls (v : FactVocabulary) (w0 u u' : World)
    (h0 : World.new v = ok w0) (hu : ReachP w0 u) (hr : ReachP u u')
    (n : String) (l : Option time.EntityId) (hn : upName u.vocabulary n)
    (k : Nat) (a : Option Std.I64) (hh : upHeld u.entities k n l a) :
    ∃ b, upHeld u'.entities k n l b ∧ upLe a b := by
  induction hr with
  | refl => exact ⟨a, hh, upLe_refl a⟩
  | @step u1 u2 t kd res hr1 hp ih =>
    obtain ⟨b, hb, hab⟩ := ih
    have h01 := reachP_trans hu hr1
    cases res with
    | Err f =>
      rw [(propose_err u1 u2 t kd f hp).1]
      exact ⟨b, hb, hab⟩
    | Ok id =>
      obtain ⟨⟨f, hv, he⟩, hc⟩ := propose_ok u1 u2 t kd id hp
      have hslots := every_world_one_fact_per_slot v w0 u1 h0 (reachP_reach h01)
      have hband := every_proposed_world_in_band v w0 u1 h0 h01
      have hn1 : upName u1.vocabulary n := by
        rw [reachP_vocab hr1]; exact hn
      obtain ⟨c, hc', hbc⟩ := apply_up u1 ⟨id, t, kd⟩ u2.entities hslots hband
        (validate_clean hv he) (validate_dir hv he) (commit_apply hc) n l hn1 k b hb
      exact ⟨c, hc', upLe_trans hab hbc⟩

end hourglass
