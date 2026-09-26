-- The rung 7 cycle law: no place sits inside itself, in every world
-- that proposals build.
import Hourglass.Counts

open Aeneas Aeneas.Std Result

namespace hourglass

open world event fact entity

/-! ## The name `located_in` -/

/-- Is the name `located_in`? -/
def locB (s : String) : Bool := decide (s = "located_in")

theorem ba_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  have key : ∀ i r, ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro i r
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r h ih =>
      rw [ih]
      have hi : i < bs.data.toList.length := by simpa using h
      rw [List.drop_eq_getElem_cons hi]
      simp [ByteArray.get!, h]
      rfl
    | case2 i r h =>
      have : bs.data.toList.length ≤ i := by simp at h ⊢; omega
      simp [List.drop_eq_nil_of_le this]
  unfold ByteArray.toList
  simp [key]

theorem bytes_eq_iff (s t : String) :
    s.toByteArray.toList.map (fun x : UInt8 => x.toNat) =
      t.toByteArray.toList.map (fun x : UInt8 => x.toNat) ↔ s = t := by
  constructor
  · intro h
    have h1 := List.map_injective_iff.2 (by intro a b hab; exact UInt8.toNat_inj.1 hab) h
    apply String.toByteArray_inj.1
    apply ByteArray.ext
    apply Array.toList_inj.1
    simpa [ba_toList] using h1
  · rintro rfl; rfl

theorem allM_eq {f : U8 × U8 → Result Bool} (hf : ∀ p, f p = ok (decide (p.1 = p.2))) :
    ∀ (l0 l1 : List U8), l0.length = l1.length →
      List.allM f (List.zip l0 l1) = ok (decide (l0 = l1))
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have ih := allM_eq hf xs ys (by simpa using h)
    simp only [List.zip_cons_cons, List.allM_cons, hf, bind_tc_ok, List.cons.injEq]
    by_cases hxy : x = y
    · simp [hxy, ih]
    · simp [hxy]; rfl

/-- `[u8] == [u8]` is list equality. -/
theorem slice_eq_u8 (s0 s1 : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s0 s1 = ok (decide (s0.val = s1.val)) := by
  unfold core.slice.cmp.PartialEqSlice.eq
  split
  · rename_i hl
    refine allM_eq (fun p => ?_) s0.val s1.val (by simpa using hl)
    simp only [core.cmp.PartialEqU8, liftFun2, core.cmp.impls.PartialEqU8.ne, bind_tc_ok]
    by_cases h : p.1 = p.2
    · simp [h]
    · have : p.1.val ≠ p.2.val := fun e => h (UScalar.eq_of_val_eq e)
      simp [h, this]
  · rename_i hl
    have : s0.val ≠ s1.val := fun e => hl (by simp [Slice.length, e])
    simp [this]

/-- The bytes of `located_in`, computed by the kernel. -/
theorem located_bytes :
    (fact.LOCATED_IN_BYTES.val.map (fun x : U8 => x.val)) =
      "located_in".toByteArray.toList.map (fun x : UInt8 => x.toNat) := by
  rw [ba_toList]
  unfold fact.LOCATED_IN_BYTES
  rw [Array.make_val]
  decide

/-- The gate and `location` test the name through its bytes. The test
    says `true` exactly for `located_in`. -/
theorem loc_test {s : String} {str : Str} {b : Bool}
    (h1 : alloc.string.String.Insts.CoreOpsDerefDerefStr.deref s = ok str)
    (h2 : fact.is_located_in str = ok b) : b = locB s := by
  unfold alloc.string.String.Insts.CoreOpsDerefDerefStr.deref at h1
  dsimp only at h1
  split at h1
  · simp only [ok.injEq] at h1
    subst h1
    simp only [fact.is_located_in, core.str.Str.as_bytes, core.array.Array.index,
      core.ops.index.IndexSlice, core.slice.index.Slice.index,
      core.slice.index.SliceIndexRangeFullSlice, core.slice.index.SliceIndexRangeFullSlice.index,
      bind_tc_ok, slice_eq_u8, ok.injEq] at h2
    subst h2
    simp only [locB]
    apply decide_eq_decide.2
    rw [Slice.from_val, Array.to_slice, Slice.from_val, ← bytes_eq_iff, ← located_bytes]
    constructor
    · intro h
      have := congrArg (List.map (fun x : U8 => x.val)) h
      simp only [List.map_map, Function.comp_def] at this
      exact this
    · intro h
      have hinj : Function.Injective (fun x : U8 => x.val) :=
        fun a c hac => UScalar.eq_of_val_eq hac
      apply List.map_injective_iff.2 hinj
      simpa [List.map_map, Function.comp_def] using h
  · -- A string longer than `Usize.max` bytes: no Rust string, and never
    -- `located_in`.
    rename_i hlong
    simp only [ok.injEq] at h1
    subst h1
    simp only [fact.is_located_in, core.str.Str.as_bytes, core.array.Array.index,
      core.ops.index.IndexSlice, core.slice.index.Slice.index,
      core.slice.index.SliceIndexRangeFullSlice, core.slice.index.SliceIndexRangeFullSlice.index,
      bind_tc_ok, slice_eq_u8, ok.injEq] at h2
    subst h2
    have hmax : 10 < Usize.max := by
      rw [Usize.max, Usize.numBits]
      rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h]
    have hloc : fact.LOCATED_IN_BYTES.val.length = 10 := by
      unfold fact.LOCATED_IN_BYTES; simp
    have hs : s ≠ "located_in" := by
      intro hs
      subst hs
      apply hlong
      have := congrArg List.length located_bytes
      simp only [List.length_map] at this
      simp only [List.length_map]
      omega
    simp only [locB, hs, decide_false]
    apply decide_eq_false
    intro h
    have := congrArg List.length h
    simp only [Slice.from_val, Array.to_slice, List.length_take, List.length_map] at this
    have hlong' : Usize.max < (s.toByteArray.toList).length := by
      simp only [List.length_map, not_le] at hlong; exact hlong
    rw [hloc] at this
    omega

/-! ## Where an entity sits -/

/-- `location`, as a pure function: the target of the first
    `located_in` fact. -/
def locOf (e : Entity) : Option time.EntityId :=
  (e.facts.val.find? (fun f => locB f.name)).bind (fun f => f.linked_to)

theorem location_loop_ok (e : Entity) :
    ∀ (k : Nat) (i : Usize) (r : Option time.EntityId), e.facts.length - i.val = k →
      entity.Entity.location_loop e i = ok r →
      r = ((e.facts.val.drop i.val).find? (fun f => locB f.name)).bind (fun f => f.linked_to) := by
  intro k
  induction k with
  | zero =>
    intro i r hn h
    rw [entity.Entity.location_loop] at h
    have hge : ¬ i < alloc.vec.Vec.len e.facts := by scalar_tac
    simp only [hge, if_false, ok.injEq] at h
    subst h
    have hle : e.facts.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hle]
  | succ k ih =>
    intro i r hn h
    rw [entity.Entity.location_loop] at h
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

theorem location_ok {e : Entity} {r : Option time.EntityId}
    (h : entity.Entity.location e = ok r) : r = locOf e := by
  have := location_loop_ok e _ 0#usize r rfl h
  simpa [locOf] using this

/-- One step up from `a`: the place of the entity at `a`. -/
def stepOf (m : ids.Ids Entity) (a : time.EntityId) : Option time.EntityId :=
  ((m : Std.ExtTreeMap Nat Entity compare)[a.val]?).bind locOf

theorem location_of_ok {w : World} {a : time.EntityId} {r : Option time.EntityId}
    (h : world.World.location_of w a = ok r) : r = stepOf w.entities a := by
  unfold world.World.location_of at h
  simp only [ids.Ids.get, bind_tc_ok] at h
  unfold stepOf
  cases he : (w.entities : Std.ExtTreeMap Nat Entity compare)[a.val]? with
  | none => simp [he] at h; exact h.symm
  | some e => simp only [he] at h; simpa using location_ok h

/-! ## The walk up the chain -/

/-- The place `j` steps up from `a`, if the chain is that long. -/
def walk (m : ids.Ids Entity) : Nat → time.EntityId → Option time.EntityId
  | 0, a => some a
  | j + 1, a => (walk m j a).bind (stepOf m)

theorem walk_add (m : ids.Ids Entity) (a : time.EntityId) (i d : Nat) :
    walk m (i + d) a = (walk m i a).bind (walk m d) := by
  induction d with
  | zero => cases walk m i a <;> rfl
  | succ d ih =>
    rw [← Nat.add_assoc, walk, ih]
    cases walk m i a <;> rfl

theorem walk_succ' (m : ids.Ids Entity) (a : time.EntityId) (j : Nat) :
    walk m (j + 1) a = (stepOf m a).bind (walk m j) := by
  rw [Nat.add_comm, walk_add]
  rfl

/-- No place sits inside itself: a walk of one step or more never
    comes back to its start. -/
def acyc (m : ids.Ids Entity) : Prop :=
  ∀ (a : time.EntityId) (d : Nat), 1 ≤ d → walk m d a ≠ some a

/-- The gate's walk: when it finds no ring, no walk of at most `k`
    steps from `at` meets the entity. -/
theorem would_cycle_loop_none (w : World) (who : time.EntityId) (n : Usize) :
    ∀ (k : Nat) (at' : time.EntityId) (hops : Usize), n.val - hops.val = k →
      world.World.would_cycle_loop w.tick w.vocabulary w.entities w.history who n at' hops = ok none →
      ∀ j ≤ k, walk w.entities j at' ≠ some who := by
  intro k
  induction k with
  | zero =>
    intro at' hops hn h j hj
    rw [world.World.would_cycle_loop] at h
    have hge : ¬ hops < n := by scalar_tac
    simp only [hge, if_false, time.EntityId.Insts.CoreCmpPartialEqEntityId.eq, bind_tc_ok] at h
    have : j = 0 := by omega
    subst this
    by_cases hw : at' = who
    · simp [hw] at h
    · simpa [walk] using hw
  | succ k ih =>
    intro at' hops hn h j hj
    rw [world.World.would_cycle_loop] at h
    have hc : hops < n := by scalar_tac
    simp only [hc, if_true, time.EntityId.Insts.CoreCmpPartialEqEntityId.eq, bind_tc_ok] at h
    by_cases hw : at' = who
    · simp [hw] at h
    · simp only [hw, decide_false, Bool.false_eq_true, if_false] at h
      rw [bind_eq_ok] at h
      obtain ⟨o, ho, h⟩ := h
      have hs : o = stepOf w.entities at' := location_of_ok (w := w) ho
      cases j with
      | zero => simpa [walk] using hw
      | succ j =>
        rw [walk_succ', ← hs]
        cases o with
        | none => simp
        | some up =>
          simp only [Option.bind_some]
          rw [bind_eq_ok] at h
          obtain ⟨h1, hh1, h⟩ := h
          obtain ⟨_, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
            (UScalar.add_spec (x := hops) (y := 1#usize) (by scalar_tac))
          rw [hadd] at hh1
          simp only [ok.injEq] at hh1
          subst hh1
          exact ih up _ (by scalar_tac) h j (by omega)


theorem would_cycle_none {w : World} {who t : time.EntityId}
    (h : world.World.would_cycle w who t = ok none) :
    ∀ j ≤ Std.ExtTreeMap.size (w.entities : Std.ExtTreeMap Nat Entity compare),
      walk w.entities j t ≠ some who := by
  unfold world.World.would_cycle ids.Ids.len at h
  split at h
  · rename_i hs
    simp only [bind_tc_ok] at h
    intro j hj
    exact would_cycle_loop_none w who _ _ t 0#usize rfl h j (by simpa using hj)
  · simp at h

theorem walk_none (m : ids.Ids Entity) (a : time.EntityId) (i d : Nat) (h : walk m i a = none) :
    walk m (i + d) a = none := by
  rw [walk_add, h]; rfl

/-- THE PIGEONHOLE. In a map with no ring, a walk of `j` steps passes
    `j` different keys, so `j` is at most the size of the map. -/
theorem walk_le_size {m : ids.Ids Entity} (hac : acyc m) {a b : time.EntityId} {j : Nat}
    (h : walk m j a = some b) :
    j ≤ Std.ExtTreeMap.size (m : Std.ExtTreeMap Nat Entity compare) := by
  classical
  -- Every stop before the last is a key of the map.
  have hkey : ∀ i < j, ∃ c, walk m i a = some c ∧
      c.val ∈ Std.ExtTreeMap.keys (m : Std.ExtTreeMap Nat Entity compare) := by
    intro i hi
    have hsome : walk m (i + 1) a ≠ none := by
      intro hn
      have := walk_none m a (i + 1) (j - (i + 1)) hn
      rw [Nat.add_sub_cancel' (by omega)] at this
      rw [this] at h; cases h
    cases hc : walk m i a with
    | none => exact absurd (by simp [walk, hc]) hsome
    | some c =>
      refine ⟨c, rfl, ?_⟩
      have hstep : stepOf m c ≠ none := by simpa [walk, hc] using hsome
      unfold stepOf at hstep
      rw [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_iff_isSome_getElem?]
      cases he : (m : Std.ExtTreeMap Nat Entity compare)[c.val]? with
      | none => simp [he] at hstep
      | some _ => rfl
  let f : Nat → Nat := fun i => ((walk m i a).map (fun c => c.val)).getD 0
  have hle := Finset.card_le_card_of_injOn f
    (s := Finset.range j) (t := (Std.ExtTreeMap.keys (m : Std.ExtTreeMap Nat Entity compare)).toFinset)
    (by
      intro i hi
      obtain ⟨c, hc, hk⟩ := hkey i (Finset.mem_range.1 hi)
      simpa [f, hc] using Std.ExtTreeMap.mem_keys.1 hk)
    (by
      intro i hi i' hi' hff
      simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
      obtain ⟨c, hc, _⟩ := hkey i hi
      obtain ⟨c', hc', _⟩ := hkey i' hi'
      simp only [f, hc, hc', Option.map_some, Option.getD_some] at hff
      have hcc : c = c' := UScalar.eq_of_val_eq hff
      subst hcc
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := walk_add m a i (i' - i)
        rw [Nat.add_sub_cancel' hlt.le, hc', hc] at this
        exact hac c (i' - i) (by omega) this.symm
      · have := walk_add m a i' (i - i')
        rw [Nat.add_sub_cancel' hlt.le, hc', hc] at this
        exact hac c (i - i') (by omega) this.symm)
  simp only [Finset.card_range] at hle
  exact le_trans hle (le_trans (List.toFinset_card_le _) (by rw [Std.ExtTreeMap.length_keys]))


/-! ## What a clean gate says -/

/-- A start of `located_in` with no fault closes no ring: no walk of
    at most the size of the map from the target meets the entity. -/
theorem start_cycle_clean {w : World} {who : time.EntityId} {nm : String} {v : Option Std.I64}
    {tgt : time.EntityId} {o o' : alloc.vec.Vec reject.Rejection}
    (h : validate.start w who nm v (some tgt) o = ok o') (he : o'.val = [])
    (hl : locB nm = true) :
    ∀ j ≤ Std.ExtTreeMap.size (w.entities : Std.ExtTreeMap Nat Entity compare),
      walk w.entities j tgt ≠ some who := by
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
    obtain ⟨_, _, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨str, hstr, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨b2, hb2, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨o4, h4, h⟩ := h
    have hr4 : o4.val <+: o4.val := List.prefix_refl _
    have p5 : o4.val <+: o'.val := grows_of (by grows) h
    have e4 := nil_of_prefix_nil p5 he
    rw [loc_test hstr hb2, hl] at h4
    simp only [if_true] at h4
    rw [bind_eq_ok] at h4
    obtain ⟨o1, ho1, h4⟩ := h4
    cases o1 with
    | none => exact would_cycle_none ho1
    | some _ =>
      simp only at h4
      exact absurd e4 (push_ne h4)

/-- What a clean gate says about the ring of a start. -/
def cycClean (w : World) : EventKind → Prop
  | .FactStart who nm _ (some tgt) => locB nm = true →
    ∀ j ≤ Std.ExtTreeMap.size (w.entities : Std.ExtTreeMap Nat Entity compare),
      walk w.entities j tgt ≠ some who
  | _ => True

theorem validate_cycle {w : World} {t : time.Tick} {k : EventKind}
    {f : alloc.vec.Vec reject.Rejection}
    (h : validate.validate w t k = ok f) (he : f.val = []) : cycClean w k := by
  unfold validate.validate at h
  rw [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out, _, h⟩ := h
  cases k with
  | FactStart who nm value lt =>
    cases lt with
    | none => trivial
    | some tgt => exact fun hl => start_cycle_clean h he hl
  | _ => trivial


/-! ## How `apply` changes one step -/

theorem find_filter_one {α : Type} (p q : α → Bool) (l : List α) (h : l.countP p ≤ 1) :
    (l.filter q).find? p = l.find? p ∨ (l.filter q).find? p = none := by
  induction l with
  | nil => left; rfl
  | cons y l ih =>
    by_cases hp : p y = true
    · have h0 : l.countP p = 0 := by
        rw [List.countP_cons, if_pos hp] at h; omega
      have hnone : (l.filter q).find? p = none := by
        rw [List.find?_eq_none]
        intro x hx
        have hx' := (List.mem_filter.1 hx).1
        have := (List.countP_eq_zero.1 h0) x hx'
        simpa using this
      by_cases hq : q y = true
      · left; simp [hq, hp]
      · right; simp [hq, hnone]
    · have hp' : p y = false := by simpa using hp
      rw [List.countP_cons, if_neg hp, Nat.add_zero] at h
      rcases ih h with h1 | h1
      · left
        by_cases hq : q y = true
        · simp [hq, hp', h1]
        · simp [hq, hp', h1]
      · right
        by_cases hq : q y = true
        · simp [hq, hp', h1]
        · simp [hq, h1]

theorem find_snoc_false {α : Type} (p : α → Bool) (l : List α) (x : α) (hx : p x = false) :
    (l ++ [x]).find? p = l.find? p := by
  rw [List.find?_append]
  simp [hx]

theorem locOf_slots {e e' : Entity}
    (h : e'.facts.val.map slotOf = e.facts.val.map slotOf) : locOf e' = locOf e := by
  have key : ∀ x : Entity, locOf x =
      ((x.facts.val.map slotOf).find? (fun s => locB s.1)).bind (fun s => s.2) := by
    intro x
    unfold locOf
    rw [List.find?_map]
    simp only [Function.comp_def, slotOf]
    cases x.facts.val.find? (fun f => locB f.name) <;> rfl
  rw [key, key e, h]

/-- The steps of `m'` are the steps of `m`, or gone. -/
def shrinks (m m' : ids.Ids Entity) : Prop :=
  ∀ a, stepOf m' a = stepOf m a ∨ stepOf m' a = none

theorem walk_shrink {m m' : ids.Ids Entity} (hs : shrinks m m') (a : time.EntityId) :
    ∀ d c, walk m' d a = some c → walk m d a = some c := by
  intro d
  induction d with
  | zero => intro c h; exact h
  | succ d ih =>
    intro c h
    simp only [walk] at h ⊢
    cases hw : walk m' d a with
    | none => simp [hw] at h
    | some y =>
      rw [hw] at h
      simp only [Option.bind_some] at h
      rw [ih y hw, Option.bind_some]
      rcases hs y with h1 | h1
      · rw [← h1]; exact h
      · rw [h1] at h; cases h

theorem acyc_shrink {m m' : ids.Ids Entity} (hs : shrinks m m') (h : acyc m) : acyc m' :=
  fun a d hd hw => h a d hd (walk_shrink hs a d a hw)

theorem step_replace (m : ids.Ids Entity) (k : Nat) (row' : Entity) (a : time.EntityId) :
    stepOf (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k row') a =
      if a.val = k then locOf row' else stepOf m a := by
  unfold stepOf
  rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase]
  by_cases ha : a.val = k
  · subst ha; simp
  · have : ¬ compare k a.val = .eq := by simpa using Ne.symm ha
    simp [this, ha]

theorem shrinks_replace {m : ids.Ids Entity} {k : Nat} {row row' : Entity}
    (hr : (m : Std.ExtTreeMap Nat Entity compare)[k]? = some row)
    (hl : locOf row' = locOf row ∨ locOf row' = none) :
    shrinks m (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k row') := by
  intro a
  rw [step_replace]
  by_cases ha : a.val = k
  · subst ha
    simp only [if_true]
    have : stepOf m a = locOf row := by simp [stepOf, hr]
    rw [this]; exact hl
  · simp [ha]

/-- THE ONE NEW EDGE. A step from `who` to `tgt`, when no walk of `m`
    from `tgt` meets `who`, closes no ring. -/
theorem acyc_link {m m' : ids.Ids Entity} {who tgt : time.EntityId} (hac : acyc m)
    (hstep : ∀ a, stepOf m' a = if a = who then some tgt else stepOf m a)
    (hgate : ∀ j ≤ Std.ExtTreeMap.size (m : Std.ExtTreeMap Nat Entity compare),
      walk m j tgt ≠ some who) : acyc m' := by
  -- A walk of `m'` is a walk of `m`, or it went through `who` and
  -- came on from `tgt`.
  have split : ∀ d a c, walk m' d a = some c →
      walk m d a = some c ∨ ((∃ e, walk m' e tgt = some c) ∧ ∃ i, walk m i a = some who) := by
    intro d
    induction d with
    | zero => intro a c h; left; exact h
    | succ d ih =>
      intro a c h
      simp only [walk] at h
      cases hw : walk m' d a with
      | none => simp [hw] at h
      | some y =>
        rw [hw, Option.bind_some, hstep] at h
        by_cases hy : y = who
        · subst hy
          simp only [if_true, Option.some.injEq] at h
          subst h
          right
          refine ⟨⟨0, rfl⟩, ?_⟩
          rcases ih a y hw with h1 | ⟨_, h1⟩
          · exact ⟨d, h1⟩
          · exact h1
        · simp only [hy, if_false] at h
          rcases ih a y hw with h1 | ⟨⟨e, he⟩, h1⟩
          · left; simp [walk, h1, h]
          · right
            refine ⟨⟨e + 1, ?_⟩, h1⟩
            simp only [walk, he, Option.bind_some, hstep, hy, if_false, h]
  -- A walk of `m` from `tgt` to `who` breaks the gate.
  have hno : ∀ j, walk m j tgt ≠ some who := by
    intro j hj
    exact hgate j (walk_le_size hac hj) hj
  intro a d hd hw
  rcases split d a a hw with h1 | ⟨⟨e, he⟩, ⟨i, hi⟩⟩
  · exact hac a d hd h1
  · rcases split e tgt a he with h2 | ⟨_, ⟨i', hi'⟩⟩
    · apply hno (e + i)
      rw [walk_add, h2, Option.bind_some, hi]
    · exact hno i' hi'


theorem locOf_filter {row row' : Entity} (q : Fact → Bool)
    (h1 : row.facts.val.countP (fun f => locB f.name) ≤ 1)
    (h2 : row'.facts.val = row.facts.val.filter q) :
    locOf row' = locOf row ∨ locOf row' = none := by
  unfold locOf
  rw [h2]
  rcases find_filter_one _ q _ h1 with h | h
  · left; rw [h]
  · right; rw [h]; rfl

/-- APPLY CLOSES NO RING, for an event with a clean gate. -/
theorem apply_acyc (w : World) (ev : Event) (m' : ids.Ids Entity)
    (hv : world.single_target w.vocabulary "located_in" = ok true)
    (h : acyc w.entities) (hot : oneTarget w.vocabulary w.entities)
    (hc : cycClean w ev.kind) (ha : World.apply w.entities w.vocabulary ev = ok m') :
    acyc m' := by
  have hone : ∀ (k : Nat) (row : Entity), (w.entities : Std.ExtTreeMap Nat Entity compare)[k]? = some row →
      row.facts.val.countP (fun f => locB f.name) ≤ 1 :=
    fun k row hr => hot k row "located_in" hr hv
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
      apply acyc_shrink _ h
      intro a
      left
      unfold stepOf
      rw [Std.ExtTreeMap.getElem?_insert]
      split
      · rename_i hka
        have hk : id.val = a.val := by simpa using hka
        have hnone : (w.entities : Std.ExtTreeMap Nat Entity compare)[a.val]? = none := by
          rw [← hk]; simpa using hnot
        simp [hnone, locOf, alloc.vec.Vec.new]
      · rfl
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
        exact acyc_shrink (shrinks_replace hr (Or.inl rfl)) h
  case FactStart who nm value lt =>
    rw [bind_eq_ok] at ha
    obtain ⟨wide, hwide, ha⟩ := ha
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
      have hvf' : ∃ q, vf.val = row.facts.val.filter q := by
        cases wide
        · simp only [Bool.false_eq_true, if_false, world.drop_slot] at hvf
          exact ⟨_, drop_slot_ok hvf⟩
        · simp only [if_true, world.drop_name] at hvf
          exact ⟨_, drop_name_ok hvf⟩
      by_cases hl : locB nm = true
      · -- A start of `located_in`: the new fact is the only one, so the
        -- step of `who` is its target.
        have hnm : nm = "located_in" := by simpa [locB] using hl
        subst hnm
        rw [hv] at hwide
        simp only [ok.injEq] at hwide
        subst hwide
        simp only [if_true, world.drop_name] at hvf
        have hloc : locOf { row with facts := v1 } = lt := by
          unfold locOf
          rw [push_val_any hv1, drop_name_ok hvf, List.find?_append]
          have : (row.facts.val.filter (fun f => !decide (f.name = "located_in"))).find?
              (fun f => locB f.name) = none := by
            rw [List.find?_eq_none]
            intro x hx
            have := (List.mem_filter.1 hx).2
            simpa [locB] using this
          rw [this]
          simp [locB]
        cases lt with
        | none =>
          exact acyc_shrink (shrinks_replace hr (Or.inr hloc)) h
        | some tgt =>
          apply acyc_link h _ (hc hl)
          intro a
          rw [step_replace, hloc]
          by_cases ha' : a = who
          · subst ha'; simp
          · have : a.val ≠ who.val := fun e => ha' (UScalar.eq_of_val_eq e)
            simp [this, ha']
      · -- Another name: the new fact is not `located_in`, and the drop
        -- only takes facts away.
        have hl' : locB nm = false := by simpa using hl
        obtain ⟨q, hq⟩ := hvf'
        apply acyc_shrink (shrinks_replace hr _) h
        have := locOf_filter q (hone _ _ hr) (row' := { row with facts := vf }) hq
        unfold locOf at this ⊢
        rw [push_val_any hv1, find_snoc_false (fun f : Fact => locB f.name) _ _ hl']
        exact this
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
      apply acyc_shrink (shrinks_replace hr (Or.inl (locOf_slots ?_))) h
      cases o1 with
      | none =>
        simp only [ok.injEq] at hvf; subst hvf; rfl
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
        simp only [alloc.vec.Vec.set_val_eq, List.set_set, List.map_set, slotOf]
        have : ((row.facts.val)[i.val].name, (row.facts.val)[i.val].linked_to) =
            (row.facts.val.map slotOf)[i.val]'(by simpa using hi) := by
          simp [slotOf]
        rw [this, List.set_getElem_self]
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
      exact acyc_shrink (shrinks_replace hr
        (locOf_filter _ (hone _ _ hr) (row' := { row with facts := vf }) (drop_slot_ok hvf))) h


/-! ## Every world that proposals build -/

theorem reachP_acyc {w u : World} (hr : ReachP w u)
    (hv : world.single_target w.vocabulary "located_in" = ok true)
    (h : acyc w.entities ∧ oneTarget w.vocabulary w.entities) :
    acyc u.entities ∧ oneTarget u.vocabulary u.entities := by
  induction hr with
  | refl => exact h
  | @step u1 u2 t k r hr1 hp ih =>
    cases r with
    | Err f => rw [(propose_err u1 u2 t k f hp).1]; exact ih
    | Ok id =>
      obtain ⟨⟨f, hvd, he⟩, hc⟩ := propose_ok u1 u2 t k id hp
      obtain ⟨_, _, hvoc⟩ := commit_ok hc
      have hv1 : world.single_target u1.vocabulary "located_in" = ok true := by
        rw [reachP_vocab hr1]; exact hv
      rw [hvoc]
      exact ⟨apply_acyc u1 ⟨id, t, k⟩ _ hv1 ih.1 ih.2 (validate_cycle hvd he) (commit_apply hc),
        apply_one_target _ _ _ _ ih.2 (commit_apply hc)⟩

/-- NO PLACE SITS INSIDE ITSELF. In every world that proposals build
    from an empty world, a walk up the `located_in` chain of one step
    or more never comes back to its start. The vocabulary must declare
    `located_in` with one target, as the crate does. -/
theorem every_proposed_world_acyclic (v : FactVocabulary) (w0 w : World)
    (h0 : World.new v = ok w0) (hv : world.single_target v "located_in" = ok true)
    (hr : ReachP w0 w) : acyc w.entities := by
  have hw0 : w0.vocabulary = v := by
    simp only [World.new, ids.Ids.new, EventHistory.new, bind_tc_ok, ok.injEq] at h0
    subst h0; rfl
  apply (reachP_acyc hr (by rw [hw0]; exact hv) _).1
  simp only [World.new, ids.Ids.new, EventHistory.new, bind_tc_ok, ok.injEq] at h0
  subst h0
  refine ⟨fun a d _ hw => ?_, fun k e n hk => by simp at hk⟩
  cases d with
  | zero => omega
  | succ d =>
    rw [walk_succ'] at hw
    simp [stepOf] at hw

theorem transGen_walk {m : ids.Ids Entity} {a b : time.EntityId}
    (h : Relation.TransGen (fun x y => stepOf m x = some y) a b) :
    ∃ d, 1 ≤ d ∧ walk m d a = some b := by
  induction h with
  | single hs => exact ⟨1, le_refl _, by simp [walk, hs]⟩
  | tail _ hs ih =>
    obtain ⟨d, hd, hw⟩ := ih
    exact ⟨d + 1, by omega, by simp [walk, hw, hs]⟩

/-- The same law, as a relation: no entity sits, through any chain of
    places, inside itself. -/
theorem no_place_inside_itself (v : FactVocabulary) (w0 w : World)
    (h0 : World.new v = ok w0) (hv : world.single_target v "located_in" = ok true)
    (hr : ReachP w0 w) (a : time.EntityId) :
    ¬ Relation.TransGen (fun x y => stepOf w.entities x = some y) a a := by
  intro h
  obtain ⟨d, hd, hw⟩ := transGen_walk h
  exact every_proposed_world_acyclic v w0 w h0 hv hr a d hd hw

end hourglass
