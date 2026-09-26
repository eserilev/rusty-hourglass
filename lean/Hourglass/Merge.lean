-- The rung 2 laws: the record merge.
--
-- `merge` joins two records name by name. The laws below hold for
-- records of any size and for any schema, with no bound.
import Hourglass.Funs

open Aeneas Aeneas.Std Result

namespace hourglass

open memory fact

/-! ## Pure mirrors of one step

Each generated function below never panics and gives the value of a
pure function. The pure functions carry the proofs. -/

/-- `Value::present`, as a pure function. -/
def memory.Value.isPresent : Value → Bool
  | .Flag b => b
  | .Number _ => true

@[simp] theorem present_eq (v : Value) : v.present = ok v.isPresent := by
  cases v
  · simp only [Value.present, memory.Value.isPresent]
    split <;> simp_all
  · simp [Value.present, memory.Value.isPresent]

/-- `join_of`, as a pure function. -/
def joinRes : FactRules → core.result.Result Join reject.Unmergeable
  | .Linked .. => .Err .TakesTarget
  | .Solo (.Flag .Up) => .Ok .Either
  | .Solo (.Flag .Down) => .Err .VanishingFlag
  | .Solo (.Flag .Free) => .Err .NoDirection
  | .Solo (.Number _ .Up) => .Ok .Larger
  | .Solo (.Number _ .Down) => .Ok .Smaller
  | .Solo (.Number _ .Free) => .Err .NoDirection

@[simp] theorem join_of_eq (r : FactRules) : join_of r = ok (joinRes r) := by
  rcases r with ⟨sh⟩ | ⟨sh, _, _, _⟩
  · rcases sh with ⟨d⟩ | ⟨_, d⟩ <;> cases d <;>
      simp [join_of, FactRules.takes_target, FactRules.shape, joinRes]
  · simp [join_of, FactRules.takes_target, joinRes]

/-- `Join::of`, as a pure function. -/
def joinVal (j : Join) (a b : Value) : Value :=
  match j, a, b with
  | .Larger, .Number x, .Number y => .Number (core.cmp.impls.OrdI64.max x y)
  | .Smaller, .Number x, .Number y => .Number (core.cmp.impls.OrdI64.min x y)
  | .Either, _, _ => .Flag true
  | _, _, _ => a

@[simp] theorem of_eq (j : Join) (a b : Value) : j.of a b = ok (joinVal j a b) := by
  cases j <;> cases a <;> cases b <;> simp [Join.of, joinVal, lift]

/-- `Record::value`: the value of a name, when it is present. -/
def val (r : Record) (k : String) : Option Value :=
  match (r : names.Names Value)[k]? with
  | some v => if v.isPresent then some v else none
  | none => none

@[simp] theorem value_eq (r : Record) (k : String) : r.value k = ok (val r k) := by
  simp only [Record.value, names.Names.get_key, bind_tc_ok, val]
  split <;> simp_all
  split_ifs <;> rfl

/-- `Record::put`: write a present value, or take the name out. -/
def putSpec (r : Record) (k : String) (v : Value) : Record :=
  if v.isPresent then Std.ExtTreeMap.insert (r : names.Names Value) k v
  else Std.ExtTreeMap.erase (r : names.Names Value) k

@[simp] theorem put_eq (r : Record) (k : String) (v : Value) :
    r.put k v = ok (putSpec r k v) := by
  simp only [Record.put, present_eq, bind_tc_ok, putSpec]
  split <;> simp [alloc.string.String.Insts.CoreCloneClone.clone,
    names.Names.insert, names.Names.remove_key]

/-- The value that the merge writes for one name, or nothing. -/
def mergeVal (s : FactVocabulary) (a b : Record) (k : String) : Option Value :=
  match (s.names : names.Names FactRules)[k]? with
  | none => none
  | some rules =>
    match joinRes rules with
    | .Err _ => none
    | .Ok j =>
      match val a k, val b k with
      | none, none => none
      | none, some y => some y
      | some x, none => some x
      | some x, some y => some (joinVal j x y)

/-- One step of the merge loop, as a pure function. -/
def stepOut (s : FactVocabulary) (a b : Record) (out : Record) (k : String) : Record :=
  match mergeVal s a b k with
  | none => out
  | some v => putSpec out k v

@[simp] theorem merge_name_eq (s : FactVocabulary) (a b : Record) (k : String) (out : Record) :
    merge_name s a b k out = ok (stepOut s a b out k) := by
  simp only [merge_name, FactVocabulary.rules_key, names.Names.get_key, bind_tc_ok,
    join_of_eq, value_eq, of_eq, put_eq, stepOut, mergeVal]
  split <;> simp_all
  split <;> simp_all
  split <;> split <;> simp_all

@[step] theorem merge_name_spec (s : FactVocabulary) (a b : Record) (k : String)
    (out : Record) : merge_name s a b k out ⦃ r => r = stepOut s a b out k ⦄ := by
  simp

/-! ## The loops -/

/-- The merge loop is a fold of the step over the names from `i`. -/
@[step] theorem merge_names_loop_spec (s : FactVocabulary) (a b : Record)
    (names : Slice String) (out : Record) (i : Usize) (hi : i.val ≤ names.length) :
    merge_names_loop s a b names out i
      ⦃ r => r = (names.val.drop i.val).foldl (stepOut s a b) out ⦄ := by
  unfold merge_names_loop
  step*
  · have hlt : i.val < names.length := by scalar_tac
    rw [r_post, out1_post, s_post, i2_post, List.drop_eq_getElem_cons hlt, List.foldl_cons]
  · have hle : names.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hle]
termination_by names.length - i.val
decreasing_by scalar_tac

/-! ## The check -/

/-- `FactRules::shape`, as a pure function. -/
def shapeOf : FactRules → Shape
  | .Solo sh => sh
  | .Linked sh _ _ _ => sh

@[simp] theorem shape_eq (r : FactRules) : r.shape = ok (shapeOf r) := by
  cases r <;> simp [FactRules.shape, shapeOf]

/-- `Band::holds`, as a pure function. -/
def bandHolds (b : Band) (n : Std.I64) : Bool :=
  if n >= b.min then decide (n <= b.max) else false

@[simp] theorem holds_eq (b : Band) (n : Std.I64) : b.holds n = ok (bandHolds b n) := by
  simp only [Band.holds, bandHolds]
  split <;> simp

/-- The fault of one name of a record, or nothing. -/
def nameFault (s : FactVocabulary) (r : Record) (k : String) : Option reject.Rejection :=
  match (r : names.Names Value)[k]? with
  | none => none
  | some value =>
    match (s.names : names.Names FactRules)[k]? with
    | none => some (.Malformed (.UnknownFact k))
    | some rules =>
      match joinRes rules with
      | .Err why => some (.Malformed (.Unmergeable k why))
      | .Ok _ =>
        match shapeOf rules, value with
        | .Flag _, .Flag _ => none
        | .Flag _, .Number _ => some (.Malformed (.TakesNoNumber k))
        | .Number _ _, .Flag _ => some (.Malformed (.NeedsNumber k))
        | .Number band _, .Number n =>
          if bandHolds band n then none
          else some (.Malformed (.OutOfBand k n band.min band.max))

theorem check_name_eq (s : FactVocabulary) (r : Record) (k : String)
    (out : alloc.vec.Vec reject.Rejection) :
    check_name s r k out =
      match nameFault s r k with
      | none => ok out
      | some x => out.push x := by
  unfold check_name nameFault
  simp only [names.Names.get_key, FactVocabulary.rules_key, bind_tc_ok, join_of_eq,
    shape_eq, holds_eq, alloc.string.String.Insts.CoreCloneClone.clone]
  cases hv : (r : names.Names Value)[k]? with
  | none => simp
  | some v =>
    cases hr : (s.names : names.Names FactRules)[k]? with
    | none => simp
    | some rules =>
      cases hj : joinRes rules with
      | Err why => simp [hj]
      | Ok j =>
        cases hs : shapeOf rules <;> cases v <;> simp [hj, hs]
        split <;> simp_all

@[step] theorem check_name_spec (s : FactVocabulary) (r : Record) (k : String)
    (out : alloc.vec.Vec reject.Rejection) (h : out.val.length < Usize.max) :
    check_name s r k out ⦃ o => o.val = out.val ++ (nameFault s r k).toList ⦄ := by
  rw [check_name_eq]
  cases nameFault s r k with
  | none => simp
  | some x => simpa using alloc.vec.Vec.push_spec out x h

/-- The check loop adds the faults of the names from `i`, in order. -/
@[step] theorem check_into_loop_spec (schema : FactVocabulary) (r : Record)
    (out : alloc.vec.Vec reject.Rejection) (names : alloc.vec.Vec String) (i : Usize)
    (hi : i.val ≤ names.length)
    (hroom : out.val.length + (names.length - i.val) ≤ Usize.max) :
    check_into_loop schema r out names i
      ⦃ o => o.val = out.val ++ (names.val.drop i.val).filterMap (nameFault schema r) ⦄ := by
  unfold check_into_loop
  step*
  · -- One name adds at most one fault, so the room stays.
    have h1 : (nameFault schema r s).toList.length ≤ 1 := by
      cases nameFault schema r s <;> simp
    have hlt : i.val < names.length := by scalar_tac
    simp only [out1_post, i2_post, List.length_append]
    omega
  · have hlt : i.val < names.length := by scalar_tac
    rw [o_post, out1_post, s_post, i2_post, List.drop_eq_getElem_cons hlt,
      List.filterMap_cons]
    cases nameFault schema r names.val[i.val] <;> simp
  · have hle : names.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hle]
termination_by names.length - i.val
decreasing_by scalar_tac

@[step] theorem merge_names_spec (s : FactVocabulary) (a b : Record) (names : Slice String)
    (out : Record) :
    merge_names s a b names out ⦃ r => r = names.val.foldl (stepOut s a b) out ⦄ := by
  unfold merge_names
  step*
  simp [r_post]

/-! ## The whole check, and the whole merge -/

@[step] theorem is_empty_spec {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty A v ⦃ b => b = v.val.isEmpty ⦄ := by
  simp [alloc.vec.Vec.is_empty]

@[step] theorem record_new_spec : Record.new ⦃ r => r = ∅ ⦄ := by
  simp [Record.new, names.Names.new]

@[step] theorem keys_spec {V : Type} (m : names.Names V) (h : m.size ≤ Usize.max) :
    names.Names.keys m ⦃ v => v.val = Std.ExtTreeMap.keys m ⦄ := by
  simp [names.Names.keys, h]

@[step] theorem check_into_spec (schema : FactVocabulary) (r : Record)
    (out : alloc.vec.Vec reject.Rejection)
    (h : out.val.length + (r : names.Names Value).size ≤ Usize.max) :
    check_into schema r out
      ⦃ o => o.val = out.val ++ (Std.ExtTreeMap.keys (r : names.Names Value)).filterMap
        (nameFault schema r) ⦄ := by
  unfold check_into
  step*
  · simp [names_post, Std.ExtTreeMap.length_keys]; omega
  · simp [o_post, names_post]

/-- A record fits the schema when no name of it has a fault. -/
def fits (s : FactVocabulary) (r : Record) : Prop :=
  ∀ k ∈ Std.ExtTreeMap.keys (r : names.Names Value), nameFault s r k = none

theorem check_spec (s : FactVocabulary) (r : Record)
    (h : (r : names.Names Value).size ≤ Usize.max) :
    check s r ⦃ o => (o.val = [] ↔ fits s r) ⦄ := by
  unfold check
  step*
  simp [*, fits, List.filterMap_eq_nil_iff]

/-- What the merge answers, as a pure function: the step over every
    name of `a`, and then over every name of `b`. -/
def mergeRec (s : FactVocabulary) (a b : Record) : Record :=
  (Std.ExtTreeMap.keys (b : names.Names Value)).foldl (stepOut s a b)
    ((Std.ExtTreeMap.keys (a : names.Names Value)).foldl (stepOut s a b) ∅)

theorem merge_spec (s : FactVocabulary) (a b : Record)
    (h : (a : names.Names Value).size + (b : names.Names Value).size ≤ Usize.max) :
    merge s a b ⦃ res =>
      match res with
      | .Ok r => fits s a ∧ fits s b ∧ r = mergeRec s a b
      | .Err _ => ¬ (fits s a ∧ fits s b) ⦄ := by
  unfold merge
  step*
  · have := List.length_filterMap_le (nameFault s a) (Std.ExtTreeMap.keys a)
    simp only [faults_post, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append]
    rw [Std.ExtTreeMap.length_keys] at this
    omega
  · have hnil : (faults1.val).isEmpty = true := by rw [← b1_post]; exact ‹b1 = true›
    simp only [faults1_post, faults_post, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
      List.nil_append, List.isEmpty_iff, List.append_eq_nil_iff,
      List.filterMap_eq_nil_iff] at hnil
    refine ⟨hnil.1, hnil.2, ?_⟩
    simp [out2_post, out1_post, out_post, v_post, v1_post, mergeRec, alloc.vec.Vec.deref]
  · rintro ⟨ha, hb⟩
    apply ‹¬b1 = true›
    simp only [b1_post, faults1_post, faults_post, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
      List.nil_append, List.isEmpty_iff, List.append_eq_nil_iff,
      List.filterMap_eq_nil_iff]
    exact ⟨ha, hb⟩

/-! ## The value of each name after the merge -/

/-- How one write of the merge changes the value at one name. -/
def upd : Option Value → Option Value → Option Value
  | none, old => old
  | some v, _ => if v.isPresent then some v else none

theorem upd_upd (o x : Option Value) : upd o (upd o x) = upd o x := by
  cases o <;> simp [upd]

theorem stepOut_get (s : FactVocabulary) (a b out : Record) (n k : String) :
    (stepOut s a b out n : names.Names Value)[k]? =
      if n = k then upd (mergeVal s a b k) (out : names.Names Value)[k]?
      else (out : names.Names Value)[k]? := by
  unfold stepOut
  by_cases hnk : n = k
  · subst hnk
    cases mergeVal s a b n <;> simp [upd, putSpec]
    split <;> simp
  · cases mergeVal s a b n <;> simp [hnk, putSpec]
    split <;> simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase, hnk]

theorem foldl_get (s : FactVocabulary) (a b : Record) (L : List String) (out : Record)
    (k : String) :
    (L.foldl (stepOut s a b) out : names.Names Value)[k]? =
      if k ∈ L then upd (mergeVal s a b k) (out : names.Names Value)[k]?
      else (out : names.Names Value)[k]? := by
  induction L generalizing out with
  | nil => simp
  | cons n L ih =>
    simp only [List.foldl_cons, ih, stepOut_get, List.mem_cons]
    by_cases hnk : n = k
    · subst hnk
      by_cases hkL : n ∈ L <;> simp [hkL, upd_upd]
    · have hkn : ¬k = n := fun h => hnk h.symm
      by_cases hkL : k ∈ L <;> simp [hkL, hnk, hkn]

theorem val_none (r : Record) (k : String) (h : k ∉ (r : names.Names Value)) :
    val r k = none := by
  simp [val, Std.ExtTreeMap.getElem?_eq_none h]

theorem val_some {r : Record} {k : String} {x : Value} (h : val r k = some x) :
    (r : names.Names Value)[k]? = some x ∧ x.isPresent := by
  unfold val at h
  cases hr : (r : names.Names Value)[k]? with
  | none => simp [hr] at h
  | some v => by_cases hp : v.isPresent <;> simp_all
theorem mergeVal_none (s : FactVocabulary) (a b : Record) (k : String)
    (ha : val a k = none) (hb : val b k = none) : mergeVal s a b k = none := by
  unfold mergeVal
  split <;> simp_all
  split <;> simp_all

/-- The value of every name after the merge. -/
theorem mergeRec_get (s : FactVocabulary) (a b : Record) (k : String) :
    (mergeRec s a b : names.Names Value)[k]? = upd (mergeVal s a b k) none := by
  unfold mergeRec
  rw [foldl_get, foldl_get]
  simp only [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.getElem?_empty]
  by_cases ha : k ∈ (a : names.Names Value) <;> by_cases hb : k ∈ (b : names.Names Value) <;>
    simp [ha, hb, upd_upd]
  rw [mergeVal_none s a b k (val_none a k ha) (val_none b k hb)]
  rfl

/-! ## What a record that fits holds -/

/-- The value of a name that fits has the shape of its join: a number
    for `Larger` and `Smaller`, and a flag for `Either`. -/
theorem fits_shape {s : FactVocabulary} {r : Record} {k : String} {x : Value}
    {rules : FactRules} {j : Join} (hf : fits s r)
    (hx : (r : names.Names Value)[k]? = some x)
    (hs : (s.names : names.Names FactRules)[k]? = some rules)
    (hj : joinRes rules = .Ok j) :
    (j = .Either → ∃ b, x = .Flag b) ∧ (j ≠ .Either → ∃ n, x = .Number n) := by
  have hk : k ∈ Std.ExtTreeMap.keys (r : names.Names Value) := by
    rw [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_iff_isSome_getElem?, hx]; rfl
  have h := hf k hk
  unfold nameFault at h
  simp only [hx, hs, hj] at h
  rcases rules with ⟨sh⟩ | ⟨sh, _, _, _⟩
  · rcases sh with ⟨d⟩ | ⟨band, d⟩ <;> cases d <;> simp [joinRes] at hj <;> subst hj <;>
      cases x <;> simp_all [shapeOf]
  · simp [joinRes] at hj

/-- The rules of a name that a fitting record holds give a join. -/
theorem fits_rules {s : FactVocabulary} {r : Record} {k : String} {x : Value}
    (hf : fits s r) (hx : (r : names.Names Value)[k]? = some x) :
    ∃ rules j, (s.names : names.Names FactRules)[k]? = some rules ∧ joinRes rules = .Ok j := by
  have hk : k ∈ Std.ExtTreeMap.keys (r : names.Names Value) := by
    rw [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_iff_isSome_getElem?, hx]; rfl
  have h := hf k hk
  unfold nameFault at h
  simp only [hx] at h
  split at h
  · simp at h
  · rename_i rules _
    split at h
    · simp at h
    · rename_i j _
      exact ⟨rules, j, by assumption, by assumption⟩

private theorem i64_ext {x y : Std.I64} (h : x.val = y.val) : x = y := by scalar_tac

theorem joinVal_comm {s : FactVocabulary} {a b : Record} {k : String} {x y : Value}
    {rules : FactRules} {j : Join} (ha : fits s a) (hb : fits s b)
    (hx : (a : names.Names Value)[k]? = some x) (hy : (b : names.Names Value)[k]? = some y)
    (hs : (s.names : names.Names FactRules)[k]? = some rules)
    (hj : joinRes rules = .Ok j) :
    joinVal j x y = joinVal j y x := by
  cases j with
  | Either => rfl
  | Larger =>
    obtain ⟨m, rfl⟩ := (fits_shape ha hx hs hj).2 (by simp)
    obtain ⟨n, rfl⟩ := (fits_shape hb hy hs hj).2 (by simp)
    simp only [joinVal, Value.Number.injEq]
    apply i64_ext; simp; omega
  | Smaller =>
    obtain ⟨m, rfl⟩ := (fits_shape ha hx hs hj).2 (by simp)
    obtain ⟨n, rfl⟩ := (fits_shape hb hy hs hj).2 (by simp)
    simp only [joinVal, Value.Number.injEq]
    apply i64_ext; simp; omega

theorem mergeVal_comm (s : FactVocabulary) (a b : Record) (k : String)
    (ha : fits s a) (hb : fits s b) : mergeVal s a b k = mergeVal s b a k := by
  unfold mergeVal
  split
  · rfl
  · rename_i rules hs
    split
    · rfl
    · rename_i j hj
      cases hva : val a k <;> cases hvb : val b k <;> simp
      rename_i x y
      exact joinVal_comm ha hb (val_some hva).1 (val_some hvb).1 hs hj

/-! ## The laws -/

/-- The records a merge reads keep only present values. `Record::set`
    and the read from JSON both keep this. -/
def wf (r : Record) : Prop :=
  ∀ (k : String) (v : Value), (r : names.Names Value)[k]? = some v → v.isPresent

private theorem merge_ok_of_spec {s : FactVocabulary} {a b : Record}
    (h : (a : names.Names Value).size + (b : names.Names Value).size ≤ Usize.max)
    (ha : fits s a) (hb : fits s b) :
    merge s a b = ok (.Ok (mergeRec s a b)) := by
  obtain ⟨res, hres, P⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1 (merge_spec s a b h)
  rw [hres]
  cases res with
  | Ok r => simp only at P; rw [P.2.2]
  | Err _ => exact absurd ⟨ha, hb⟩ P

private theorem fits_of_merge_ok {s : FactVocabulary} {a b r : Record}
    (h : (a : names.Names Value).size + (b : names.Names Value).size ≤ Usize.max)
    (hm : merge s a b = ok (.Ok r)) :
    fits s a ∧ fits s b ∧ r = mergeRec s a b := by
  obtain ⟨res, hres, P⟩ := (Aeneas.Std.WP.spec_equiv_exists _ _).1 (merge_spec s a b h)
  rw [hm] at hres
  simp only [ok.injEq] at hres
  subst hres
  exact P

/-- THE MERGE IS COMMUTATIVE. Two records merge to the same record in
    either order. When a record does not fit, both orders refuse; the
    faults come in the order of the records. -/
theorem merge_comm (s : FactVocabulary) (a b r : Record)
    (h : (a : names.Names Value).size + (b : names.Names Value).size ≤ Usize.max) :
    merge s a b = ok (.Ok r) ↔ merge s b a = ok (.Ok r) := by
  have h' : (b : names.Names Value).size + (a : names.Names Value).size ≤ Usize.max := by omega
  have key : ∀ (x y : Record),
      (x : names.Names Value).size + (y : names.Names Value).size ≤ Usize.max →
      merge s x y = ok (.Ok r) → merge s y x = ok (.Ok r) := by
    intro x y hxy hm
    have hyx : (y : names.Names Value).size + (x : names.Names Value).size ≤ Usize.max := by
      omega
    obtain ⟨hx, hy, rfl⟩ := fits_of_merge_ok hxy hm
    rw [merge_ok_of_spec hyx hy hx]
    congr 2
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    rw [mergeRec_get, mergeRec_get, mergeVal_comm s y x k hy hx]
  exact ⟨key a b h, key b a h'⟩

theorem joinVal_self {s : FactVocabulary} {a : Record} {k : String} {x : Value}
    {rules : FactRules} {j : Join} (ha : fits s a) (hw : wf a)
    (hx : (a : names.Names Value)[k]? = some x)
    (hs : (s.names : names.Names FactRules)[k]? = some rules)
    (hj : joinRes rules = .Ok j) :
    joinVal j x x = x := by
  cases j with
  | Either =>
    obtain ⟨b, rfl⟩ := (fits_shape ha hx hs hj).1 rfl
    have := hw k _ hx
    simp_all [joinVal, memory.Value.isPresent]
  | Larger =>
    obtain ⟨m, rfl⟩ := (fits_shape ha hx hs hj).2 (by simp)
    simp only [joinVal, Value.Number.injEq]
    apply i64_ext; simp
  | Smaller =>
    obtain ⟨m, rfl⟩ := (fits_shape ha hx hs hj).2 (by simp)
    simp only [joinVal, Value.Number.injEq]
    apply i64_ext; simp

/-- A MERGE WITH ITSELF CHANGES NOTHING. So a merge that runs twice
    answers what it answered once. -/
theorem merge_self (s : FactVocabulary) (a : Record)
    (h : (a : names.Names Value).size + (a : names.Names Value).size ≤ Usize.max)
    (hf : fits s a) (hw : wf a) :
    merge s a a = ok (.Ok a) := by
  rw [merge_ok_of_spec h hf hf]
  congr 2
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [mergeRec_get]
  cases hx : (a : names.Names Value)[k]? with
  | none =>
    have hn : k ∉ (a : names.Names Value) := by
      rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hx]; simp
    rw [mergeVal_none s a a k (val_none a k hn) (val_none a k hn)]
    rfl
  | some x =>
    obtain ⟨rules, j, hs, hj⟩ := fits_rules hf hx
    have hp := hw k x hx
    have hv : val a k = some x := by simp [val, hx, hp]
    simp [mergeVal, hs, hj, hv, joinVal_self hf hw hx hs hj, upd, hp]

/-- AN EMPTY RECORD CHANGES NOTHING. A device that remembers nothing
    takes the other record as it is. -/
theorem merge_empty (s : FactVocabulary) (a : Record)
    (h : (a : names.Names Value).size ≤ Usize.max)
    (hf : fits s a) (hw : wf a) :
    merge s a (∅ : names.Names Value) = ok (.Ok a) := by
  have he : fits s (∅ : names.Names Value) := by
    intro k hk; simp [Std.ExtTreeMap.mem_keys] at hk
  rw [merge_ok_of_spec (by simpa using h) hf he]
  congr 2
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [mergeRec_get]
  have h0 : val (∅ : names.Names Value) k = none := by simp [val]
  cases hx : (a : names.Names Value)[k]? with
  | none =>
    have hn : k ∉ (a : names.Names Value) := by
      rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hx]; simp
    rw [mergeVal_none s a _ k (val_none a k hn) h0]
    rfl
  | some x =>
    obtain ⟨rules, j, hs, hj⟩ := fits_rules hf hx
    have hp := hw k x hx
    have hv : val a k = some x := by simp [val, hx, hp]
    simp [mergeVal, hs, hj, hv, h0, upd, hp]

end hourglass
