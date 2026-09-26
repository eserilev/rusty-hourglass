-- The rung 10 law: a batch of proposals is a sequence of single
-- proposals, so every law holds after a batch too.
import Hourglass.Referee

open Aeneas Aeneas.Std Result

namespace hourglass

open world event fact entity

/-- Propose each kind in order, at one tick. -/
def proposeList (w : World) (t : time.Tick) :
    List EventKind → Result (List (core.result.Result time.EventId (alloc.vec.Vec reject.Rejection)) × World)
  | [] => ok ([], w)
  | k :: ks => do
    let p ← World.propose w t k
    let q ← proposeList p.2 t ks
    ok (p.1 :: q.1, q.2)

theorem propose_all_loop_eq (t : time.Tick) (kinds : alloc.vec.Vec EventKind) :
    ∀ (n : Nat) (w : World) (out : alloc.vec.Vec (core.result.Result time.EventId (alloc.vec.Vec reject.Rejection)))
      (i : Usize) out' w', kinds.length - i.val = n →
      World.propose_all_loop w t kinds out i = ok (out', w') →
      ∃ rs, proposeList w t (kinds.val.drop i.val) = ok (rs, w') ∧ out'.val = out.val ++ rs := by
  intro n
  induction n with
  | zero =>
    intro w out i out' w' hn h
    rw [World.propose_all_loop] at h
    have hge : ¬ i < alloc.vec.Vec.len kinds := by scalar_tac
    have hle : kinds.val.length ≤ i.val := by scalar_tac
    simp only [hge, if_false, ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp [List.drop_eq_nil_of_le hle, proposeList], by simp⟩
  | succ n ih =>
    intro w out i out' w' hn h
    rw [World.propose_all_loop] at h
    have hc : i < alloc.vec.Vec.len kinds := by scalar_tac
    have hlt : i.val < kinds.val.length := by scalar_tac
    simp [hc, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hlt] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨r, w1⟩, hp, h⟩ := h
    simp at h
    rw [bind_eq_ok] at h
    obtain ⟨out1, hout1, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨i2, hi2, h⟩ := h
    obtain ⟨j, hadd, hval⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hj : j.val = i.val + 1 := by simpa using hval
    rw [hadd] at hi2
    simp only [ok.injEq] at hi2
    subst hi2
    obtain ⟨rs, hrs, hout⟩ := ih w1 out1 _ out' w' (by scalar_tac) h
    refine ⟨r :: rs, ?_, ?_⟩
    · rw [List.drop_eq_getElem_cons hlt]
      simp only [proposeList, hp, bind_tc_ok]
      rw [← hj, hrs]
      simp
    · rw [hout, push_val_any hout1]
      simp

/-- A BATCH IS A SEQUENCE. `propose_all` gives exactly the answers and
    the world of proposing each kind in order. -/
theorem propose_all_eq {w w' : World} {t : time.Tick} {kinds : alloc.vec.Vec EventKind}
    {out : alloc.vec.Vec (core.result.Result time.EventId (alloc.vec.Vec reject.Rejection))}
    (h : World.propose_all w t kinds = ok (out, w')) :
    proposeList w t kinds.val = ok (out.val, w') := by
  obtain ⟨rs, hrs, hout⟩ := propose_all_loop_eq t kinds _ w _ 0#usize out w' rfl h
  rw [hout]
  simpa [alloc.vec.Vec.new] using hrs

theorem proposeList_reach {t : time.Tick} :
    ∀ (ks : List EventKind) (w w' : World) rs, proposeList w t ks = ok (rs, w') → ReachP w w'
  | [], w, w', rs, h => by
    simp only [proposeList, ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ReachP.refl _
  | k :: ks, w, w', rs, h => by
    simp only [proposeList] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨r, w1⟩, hp, h⟩ := h
    rw [bind_eq_ok] at h
    obtain ⟨⟨rs1, w2⟩, hrest, h⟩ := h
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact reachP_trans (ReachP.step (ReachP.refl w) hp) (proposeList_reach ks w1 w2 rs1 hrest)

/-- EVERY LAW HOLDS AFTER A BATCH. A world that proposals build, and
    then one batch: the referee passes it. -/
theorem every_batch_verifies (v : FactVocabulary) (w0 w w' : World) (t : time.Tick)
    (kinds : alloc.vec.Vec EventKind)
    (out : alloc.vec.Vec (core.result.Result time.EventId (alloc.vec.Vec reject.Rejection)))
    (h0 : World.new v = ok w0) (hv : world.single_target v "located_in" = ok true)
    (hr : ReachP w0 w) (hb : World.propose_all w t kinds = ok (out, w')) :
    verify.verify w' = ok true :=
  every_proposed_world_verifies v w0 w' h0 hv
    (reachP_trans hr (proposeList_reach _ w w' _ (propose_all_eq hb)))

end hourglass
