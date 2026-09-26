-- The rung 3 laws: the world and its history.
--
-- `apply` and `validate` stay opaque (FunsExternal.lean), so each law
-- below holds for every `apply` and every `validate`. The laws are
-- about the history discipline: what `commit`, `replay`, `rewind`,
-- and `propose` do with the history, the tick, and the entities.
import Hourglass.Funs

open Aeneas Aeneas.Std Result

namespace hourglass

open world event fact

/-! ## A clone gives the same value -/

@[simp] theorem entityId_clone (x : time.EntityId) :
    time.EntityId.Insts.CoreCloneClone.clone x = ok x := by
  simp [time.EntityId.Insts.CoreCloneClone.clone]

@[simp] theorem entityType_clone (x : entity.EntityType) :
    entity.EntityType.Insts.CoreCloneClone.clone x = ok x := by
  cases x <;> simp [entity.EntityType.Insts.CoreCloneClone.clone]

@[simp] theorem option_clone {T : Type} (inst : core.clone.Clone T) (o : Option T)
    (h : ∀ x, inst.clone x = ok x) :
    core.option.Option.Insts.CoreCloneClone.clone inst o = ok o := by
  cases o <;> simp [core.option.Option.Insts.CoreCloneClone.clone, h]

@[simp] theorem eventKind_clone (k : EventKind) :
    EventKind.Insts.CoreCloneClone.clone k = ok k := by
  cases k <;> simp [EventKind.Insts.CoreCloneClone.clone,
    alloc.string.String.Insts.CoreCloneClone.clone, option_clone,
    time.EntityId.Insts.CoreCloneClone, core.clone.CloneI64, lift]

@[simp] theorem vocabulary_clone (v : FactVocabulary) :
    FactVocabulary.Insts.CoreCloneClone.clone v = ok v := by
  simp [FactVocabulary.Insts.CoreCloneClone.clone,
    names.Names.Insts.CoreCloneClone.clone, lift]

/-! ## One commit, and one step of replay -/

/-- What a commit that succeeds did. -/
theorem commit_ok {w w' : World} {t : time.Tick} {k : EventKind} {id : time.EventId}
    (hc : World.commit w t k = ok (id, w')) :
    EventHistory.next_id w.history = ok id ∧
    alloc.vec.Vec.push w.history ⟨id, t, k⟩ = ok w'.history ∧
    w'.vocabulary = w.vocabulary := by
  unfold World.commit at hc
  cases hn : EventHistory.next_id w.history
  case ret id0 =>
    simp only [hn, bind_tc_ok] at hc
    cases ha : _root_.world.World.apply w.entities w.vocabulary ⟨id0, t, k⟩
    case ret bm =>
      simp only [ha, bind_tc_ok, EventHistory.append] at hc
      cases hp : alloc.vec.Vec.push w.history ⟨id0, t, k⟩
      case ret eh =>
        simp only [hp, bind_tc_ok, time.Tick.Insts.CoreCmpPartialOrdTick.gt] at hc
        split at hc <;> simp only [ok.injEq, Prod.mk.injEq] at hc <;>
          obtain ⟨rfl, rfl⟩ := hc <;> simp [hp]
      all_goals simp [hp] at hc
    all_goals simp [ha] at hc
  all_goals simp [hn] at hc

/-- THE STEP LAW. A step of replay on the event that a commit made
    gives the world the commit gave. -/
theorem replay_one_of_commit {w w' : World} {t : time.Tick} {k : EventKind}
    {id : time.EventId} (hc : World.commit w t k = ok (id, w')) :
    World.replay_one w ⟨id, t, k⟩ = ok w' := by
  unfold World.commit at hc
  unfold World.replay_one
  simp only [eventKind_clone, bind_tc_ok, EventHistory.push]
  cases hn : EventHistory.next_id w.history
  case ret id0 =>
    simp only [hn, bind_tc_ok] at hc ⊢
    cases ha : _root_.world.World.apply w.entities w.vocabulary ⟨id0, t, k⟩
    case ret bm =>
      simp only [ha, bind_tc_ok, EventHistory.append] at hc
      cases hp : alloc.vec.Vec.push w.history ⟨id0, t, k⟩
      case ret eh =>
        simp only [hp, bind_tc_ok, time.Tick.Insts.CoreCmpPartialOrdTick.gt] at hc
        split at hc <;> simp only [ok.injEq, Prod.mk.injEq] at hc <;>
          obtain ⟨rfl, rfl⟩ := hc <;>
          simp_all [time.Tick.Insts.CoreCmpPartialOrdTick.gt, UScalar.lt_equiv]
      all_goals simp [hp] at hc
    all_goals simp [ha] at hc
  all_goals simp [hn] at hc

/-! ## Replay is a fold of the step -/

theorem replay_loop_eq (s : Slice Event) :
    ∀ (n : Nat) (out : World) (i : Usize), s.length - i.val = n → i.val ≤ s.length →
    World.replay_loop out s i = (s.val.drop i.val).foldlM World.replay_one out := by
  intro n
  induction n with
  | zero =>
    intro out i hn hi
    have hle : s.length ≤ i.val := by omega
    have hge : ¬ i < Slice.len s := by scalar_tac
    rw [World.replay_loop]
    simp [hge, List.drop_eq_nil_of_le hle]
    rfl
  | succ n ih =>
    intro out i hn hi
    have hlt : i.val < s.length := by omega
    have hc : i < Slice.len s := by scalar_tac
    have hix : Slice.index_usize s i = ok s.val[i.val] := by
      simp [Slice.index_usize, hlt]
      rfl
    obtain ⟨i2, hadd, hi2⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [World.replay_loop]
    simp only [hc, if_true, hix, bind_tc_ok, hadd]
    rw [List.drop_eq_getElem_cons hlt, List.foldlM_cons]
    congr 1
    funext o
    rw [ih o i2 (by scalar_tac) (by scalar_tac), hi2]
    simp

/-- `World::new` never fails, and it starts with an empty history. -/
theorem new_ok (v : FactVocabulary) :
    ∃ w0, World.new v = ok w0 ∧ w0.history.val = [] ∧ w0.vocabulary = v := by
  simp [World.new, alloc.collections.btree.map.BTreeMapKVGlobal.new, EventHistory.new]

theorem replay_eq (v : FactVocabulary) (h : EventHistory) (w0 : World)
    (h0 : World.new v = ok w0) :
    World.replay v h = h.val.foldlM World.replay_one w0 := by
  unfold World.replay
  simp only [h0, bind_tc_ok, EventHistory.events]
  rw [replay_loop_eq _ _ w0 0#usize rfl (by simp)]
  simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]

/-! ## The worlds that commits reach -/

/-- `Reach w u`: commits turn the world `w` into the world `u`. -/
inductive Reach : World → World → Prop
  | refl (w : World) : Reach w w
  | step {w u u' : World} {t : time.Tick} {k : EventKind} {id : time.EventId} :
      Reach w u → World.commit u t k = ok (id, u') → Reach w u'

theorem push_val {v v' : alloc.vec.Vec Event} {x : Event}
    (h : alloc.vec.Vec.push v x = ok v') : v'.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · simp only [ok.injEq] at h
    subst h
    simp [alloc.vec.Vec.from_val]
  · simp at h

/-- A reached world adds events to the history, keeps the vocabulary,
    and the steps of replay over the new events give that world. -/
theorem reach_history {w u : World} (h : Reach w u) :
    ∃ more : List Event, u.history.val = w.history.val ++ more ∧
      more.foldlM World.replay_one w = ok u ∧ u.vocabulary = w.vocabulary := by
  induction h with
  | refl => exact ⟨[], by simp, rfl, rfl⟩
  | @step u u' t k id _ hc ih =>
    obtain ⟨more, hh, hf, hv⟩ := ih
    obtain ⟨_, hp, hv'⟩ := commit_ok hc
    refine ⟨more ++ [⟨id, t, k⟩], ?_, ?_, ?_⟩
    · rw [push_val hp, hh, List.append_assoc]
    · rw [List.foldlM_append, hf]
      simpa using replay_one_of_commit hc
    · rw [hv', hv]

/-- REPLAY GIVES THE LIVE WORLD. A world that commits built from an
    empty world is exactly the replay of its own history. -/
theorem replay_is_the_world (v : FactVocabulary) (w0 w : World)
    (h0 : World.new v = ok w0) (hr : Reach w0 w) :
    World.replay v w.history = ok w := by
  obtain ⟨more, hh, hf, _⟩ := reach_history hr
  rw [replay_eq v w.history w0 h0, hh]
  obtain ⟨w1, h1, he, _⟩ := new_ok v
  rw [h0] at h1
  simp only [ok.injEq] at h1
  subst h1
  rw [he, List.nil_append, hf]

/-! ## Rewind -/

theorem umax_lt (ty : UScalarTy) : UScalar.max ty < 2 ^ ty.numBits := by
  rw [UScalar.max_def]
  have : 0 < 2 ^ ty.numBits := Nat.two_pow_pos _
  omega

theorem sat_add_val {ty : UScalarTy} (x y : UScalar ty) :
    (UScalar.saturating_add x y).val = min (UScalar.max ty) (x.val + y.val) := by
  have h : Min.min (UScalar.max ty) (x.val + y.val) < 2 ^ ty.numBits :=
    lt_of_le_of_lt (min_le_left _ _) (umax_lt ty)
  show (BitVec.ofNat ty.numBits _).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- REWIND IS EXACT. A world `u` that commits reached, and then more
    commits after it: a rewind to the last event of `u` gives `u`
    back, as if the later events never happened. -/
theorem rewind_is_exact (v : FactVocabulary) (w0 u u' : World)
    (h0 : World.new v = ok w0) (hu : Reach w0 u) (hu' : Reach u u')
    (after : time.EventId) (hafter : after.val + 1 = u.history.val.length) :
    World.rewind u' after = ok u := by
  obtain ⟨w1, h1, _, hv1⟩ := new_ok v
  rw [h0] at h1
  simp only [ok.injEq] at h1
  subst h1
  obtain ⟨_, _, _, hvu⟩ := reach_history hu
  obtain ⟨more, hh, _, hvu'⟩ := reach_history hu'
  have hrep := replay_is_the_world v w0 u h0 hu
  have hlen := u.history.property
  have hci : (UScalar.cast .Usize after).val = after.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    have := umax_lt UScalarTy.Usize
    rw [UScalar.max_USize_eq] at this
    omega
  have hkeep : (core.num.Usize.saturating_add (UScalar.cast .Usize after) 1#usize).val =
      u.history.val.length := by
    simp only [core.num.Usize.saturating_add, sat_add_val, hci]
    simp
    scalar_tac
  unfold World.rewind EventHistory.truncate
  simp only [lift, bind_tc_ok, vocabulary_clone, core.mem.take,
    EventHistory.Insts.CoreDefaultDefault.default,
    alloc.vec.Vec.Insts.CoreDefaultDefault.default]
  have hvoc : u'.vocabulary = v := by rw [hvu', hvu, hv1]
  split
  · simp only [alloc.vec.Vec.truncate, bind_tc_ok, hvoc]
    rw [← hrep]
    show World.replay v (alloc.vec.Vec.from _ _) = World.replay v u.history
    congr 1
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.from_val, hkeep, hh, List.take_left]
  · rename_i hn
    have hmore : more = [] := by
      have : u'.history.val.length = u.history.val.length + more.length := by
        rw [hh, List.length_append]
      have : ¬ (u.history.val.length < u'.history.val.length) := by
        intro hl; apply hn; scalar_tac
      apply List.eq_nil_of_length_eq_zero; omega
    simp only [hvoc, bind_tc_ok]
    rw [← hrep]
    show World.replay v u'.history = World.replay v u.history
    congr 1
    apply alloc.vec.Vec.ext
    rw [hh, hmore, List.append_nil]

/-! ## Propose -/

/-- A PROPOSAL THAT PASSES IS A COMMIT. `propose` lands an event only
    when `validate` finds no fault, and then it is exactly `commit`. -/
theorem propose_ok (w w' : World) (t : time.Tick) (k : EventKind) (id : time.EventId)
    (h : World.propose w t k = ok (.Ok id, w')) :
    (∃ f, validate.validate w t k = ok f ∧ f.val = []) ∧ World.commit w t k = ok (id, w') := by
  unfold World.propose at h
  cases hv : validate.validate w t k
  case ret f =>
    simp only [hv, bind_tc_ok, alloc.vec.Vec.is_empty] at h
    split at h
    · rename_i he
      refine ⟨⟨f, rfl, by simpa using he⟩, ?_⟩
      cases hc : World.commit w t k
      case ret r =>
        obtain ⟨id', w''⟩ := r
        simp only [hc, bind_tc_ok] at h
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      all_goals simp [hc] at h
    · simp at h
  all_goals simp [hv] at h

/-- A REFUSED PROPOSAL CHANGES NOTHING. The world stays the same, and
    the faults are the faults that `validate` found. -/
theorem propose_err (w w' : World) (t : time.Tick) (k : EventKind)
    (f : alloc.vec.Vec reject.Rejection)
    (h : World.propose w t k = ok (.Err f, w')) :
    w' = w ∧ validate.validate w t k = ok f ∧ f.val ≠ [] := by
  unfold World.propose at h
  cases hv : validate.validate w t k
  case ret f0 =>
    simp only [hv, bind_tc_ok, alloc.vec.Vec.is_empty] at h
    split at h
    · cases hc : World.commit w t k
      case ret r =>
        obtain ⟨id', w''⟩ := r
        simp [hc] at h
      all_goals simp [hc] at h
    · rename_i hne
      simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, by simpa using hne⟩
  all_goals simp [hv] at h

/-- So a world that any mix of proposals and commits built replays
    exactly: a proposal is a commit or no change at all. -/
theorem reach_propose {w0 u u' : World} {t : time.Tick} {k : EventKind}
    {r : core.result.Result time.EventId (alloc.vec.Vec reject.Rejection)}
    (hu : Reach w0 u) (h : World.propose u t k = ok (r, u')) : Reach w0 u' := by
  cases r with
  | Ok id => exact Reach.step hu (propose_ok u u' t k id h).2
  | Err f => rw [(propose_err u u' t k f h).1]; exact hu

end hourglass
