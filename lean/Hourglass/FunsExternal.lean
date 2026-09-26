-- The external model: the std items that the extracted code calls.
--
-- Aeneas writes these items as opaque axioms, with no body. A proof
-- cannot see inside an axiom, so this file gives each item a body.
-- Each body states the Rust semantics of the item. This file is the
-- trusted part of the proofs: read it before you trust a theorem.
-- extract.sh never overwrites it, and it writes the new Aeneas
-- template beside it as FunsExternal_Template.lean for a diff.
module
public import Aeneas
public import Hourglass.Types
public import Std.Data.ExtTreeMap
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

open hourglass

/-- `impl PartialEq for Option<T>`: two `None` values are equal, two
    `Some` values compare their contents, and a mixed pair is not equal.
    That is the derive in core. -/
@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
  {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) :
  Option T → Option T → Result Bool
  | none, none => ok true
  | some x, some y => cmpPartialEqInst.eq x y
  | _, _ => ok false

/-- `Tick < Tick`. `Tick` is `struct Tick(pub u64)` with
    `#[derive(PartialOrd)]`. The derive compares the one field, and the
    default `lt` is `partial_cmp == Some(Less)`, so it is `<` on u64. -/
def time.Tick.Insts.CoreCmpPartialOrdTick.lt
  (a b : time.Tick) : Result Bool :=
  ok (a < b)

/-- `Tick >= Tick`, by the same derive: `>=` on u64. -/
def time.Tick.Insts.CoreCmpPartialOrdTick.ge
  (a b : time.Tick) : Result Bool :=
  ok (a >= b)

/-- `String::clone` gives an equal string. -/
@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (s : String) : Result String :=
  ok s

/-- `Vec::is_empty` is `len() == 0`. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
def alloc.vec.Vec.is_empty {T : Type} (_A : Type) (v : alloc.vec.Vec T) : Result Bool :=
  ok v.val.isEmpty

/-! ## `Names<V>`, the map from a name to a value

Each operation is the operation of the same name on `ExtTreeMap`
(see TypesExternal.lean). The tests in `src/names.rs` check the laws
of each one against the Rust code. -/

/-- `Names::new` is the empty map. -/
def names.Names.new (V : Type) : Result (names.Names V) :=
  ok ∅

/-- `Names::get_key` is the value of the name, if the map holds it. -/
def names.Names.get_key {V : Type} (m : names.Names V) (k : String) :
    Result (Option V) :=
  ok m[k]?

/-- `Names::insert` adds the name, or replaces its value. -/
def names.Names.insert {V : Type} (m : names.Names V) (k : String) (v : V) :
    Result (names.Names V) :=
  ok (Std.ExtTreeMap.insert m k v)

/-- `Names::remove_key` takes the name out. A name the map does not
    hold changes nothing. -/
def names.Names.remove_key {V : Type} (m : names.Names V) (k : String) :
    Result (names.Names V) :=
  ok (Std.ExtTreeMap.erase m k)

/-- `Names::keys` gives every name one time, in ascending order. A
    `Vec` holds at most `usize::MAX` items. A map that large does not
    fit in memory, so the model panics there. -/
def names.Names.keys {V : Type} (m : names.Names V) :
    Result (alloc.vec.Vec String) :=
  if h : (Std.ExtTreeMap.keys m).length ≤ Usize.max then
    ok (alloc.vec.Vec.from (Std.ExtTreeMap.keys m) h)
  else fail .panic


/-- `Tick > Tick`, by the derive of `Tick`: `>` on u64. -/
def time.Tick.Insts.CoreCmpPartialOrdTick.gt
  (a b : time.Tick) : Result Bool :=
  ok (a > b)

/-- `Option::clone` clones the content. -/
@[rust_fun
  "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone
  {T : Type} (cloneCloneInst : core.clone.Clone T) :
  Option T → Result (Option T)
  | none => ok none
  | some x => do
    let y ← cloneCloneInst.clone x
    ok (some y)

/-- `std::mem::take` gives the old value and leaves the default. -/
@[rust_fun "core::mem::take"]
def core.mem.take
  {T : Type} (defaultDefaultInst : core.default.Default T) (x : T) :
  Result (T × T) := do
  let d ← defaultDefaultInst.default
  ok (x, d)

/-- `Vec::default` is the empty vector. -/
@[rust_fun
  "alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default"]
def alloc.vec.Vec.Insts.CoreDefaultDefault.default
  (T : Type) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

/-- `Vec::truncate(n)` keeps the first `n` items. A vector with `n`
    items or fewer stays the same. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::truncate"]
def alloc.vec.Vec.truncate
  {T : Type} (_A : Type) (v : alloc.vec.Vec T) (n : Std.Usize) :
  Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.from (v.val.take n.val)
    (by have := v.property; simp only [List.length_take]; omega))

/-- `Names::clone` gives an equal map. -/
def names.Names.Insts.CoreCloneClone.clone
  {V : Type} (_corecloneCloneInst : core.clone.Clone V) (m : names.Names V) :
  Result (names.Names V) :=
  ok m

/-- `BTreeMap::new` and `BTreeMap::clone`, on the placeholder model of
    TypesExternal.lean. -/
@[rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, alloc::alloc::Global>}::new"]
def alloc.collections.btree.map.BTreeMapKVGlobal.new
  (K : Type) (V : Type) :
  Result (alloc.collections.btree.map.BTreeMap K V Global) :=
  ok ([] : List (K × V))

@[rust_fun
  "alloc::collections::btree::map::{core::clone::Clone<alloc::collections::btree::map::BTreeMap<@K, @V, @A>>}::clone"]
def alloc.collections.btree.map.BTreeMap.Insts.CoreCloneClone.clone
  {K : Type} {V : Type} {A : Type} (_corecloneCloneInst : core.clone.Clone K)
  (_corecloneCloneInst1 : core.clone.Clone V) (_coreallocAllocatorCloneInst :
  core.alloc.AllocatorClone A) (m : alloc.collections.btree.map.BTreeMap K V A) :
  Result (alloc.collections.btree.map.BTreeMap K V A) :=
  ok m

/-- `String == String` compares the contents. -/
@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqString.eq (a b : String) : Result Bool :=
  ok (decide (a = b))

/-- `String` as `&str`: the UTF-8 bytes of the string. A Rust string
    holds at most `isize::MAX` bytes, so the bound always holds. -/
@[rust_fun "alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref"]
def alloc.string.String.Insts.CoreOpsDerefDerefStr.deref (s : String) : Result Str :=
  let l : List U8 := s.toByteArray.toList.map
    (fun x => UScalar.ofNatCore x.toNat (by have := x.toNat_lt; simpa using this))
  if h : l.length ≤ Usize.max then ok (Slice.from l h) else fail .panic

/-- `str::as_bytes`: the model of a `str` is its bytes already. -/
@[rust_fun "core::str::{str}::as_bytes"]
def core.str.Str.as_bytes (s : Str) : Result (Slice U8) :=
  ok s

/-- `str == str` compares the bytes. -/
@[rust_fun "core::str::traits::{core::cmp::PartialEq<str, str>}::eq"]
def Str.Insts.CoreCmpPartialEqStr.eq (a b : Str) : Result Bool :=
  ok (decide (a = b))

/-- `Vec::remove(i)` takes the item at `i` out and shifts the rest
    left. It panics when `i` is not below the length. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::remove"]
def alloc.vec.Vec.remove {T : Type} (_A : Type) (v : alloc.vec.Vec T) (i : Std.Usize) :
    Result (T × alloc.vec.Vec T) :=
  if h : i.val < v.val.length then
    ok (v.val[i.val], alloc.vec.Vec.from (v.val.eraseIdx i.val)
      (by have := v.property; simp only [List.length_eraseIdx, h, if_true]; omega))
  else fail .panic

/-! ## `Ids<V>`, the map from an entity id to a value

Each operation is the `ExtTreeMap` operation of the same name, at the
number of the id (see TypesExternal.lean). The tests in `src/ids.rs`
check the laws of each one against the Rust code. -/

/-- `Ids::new` is the empty map. -/
def ids.Ids.new (V : Type) : Result (ids.Ids V) :=
  ok ∅

/-- `Ids::contains` says whether the map holds the id. -/
def ids.Ids.contains {V : Type} (m : ids.Ids V) (id : time.EntityId) : Result Bool :=
  ok (Std.ExtTreeMap.contains m id.val)

/-- `Ids::insert` adds the id, or replaces its value. -/
def ids.Ids.insert {V : Type} (m : ids.Ids V) (id : time.EntityId) (v : V) :
    Result (ids.Ids V) :=
  ok (Std.ExtTreeMap.insert m id.val v)

/-- `Ids::take` gives the value of the id and takes it out. -/
def ids.Ids.take {V : Type} (m : ids.Ids V) (id : time.EntityId) :
    Result (Option V × ids.Ids V) :=
  ok (m[id.val]?, Std.ExtTreeMap.erase m id.val)

/-- `Option != Option` is the negation of `==`. -/
@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::ne"]
def core.option.Option.Insts.CoreCmpPartialEqOption.ne
  {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (a b : Option T) : Result Bool := do
  let e ← core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst a b
  ok (!e)

/-- `EntityId != EntityId`, by the derive: `!=` on the u32. -/
def time.EntityId.Insts.CoreCmpPartialEqEntityId.ne (a b : time.EntityId) : Result Bool :=
  ok (decide (a ≠ b))

/-- `Ids::get` is the value of the id, if the map holds it. -/
def ids.Ids.get {V : Type} (m : ids.Ids V) (id : time.EntityId) : Result (Option V) :=
  ok m[id.val]?

/-- `Ids::ids` gives every id one time, in ascending order. The model
    keys are numbers, and each key of an `Ids` map comes from an
    `EntityId`, a `u32`. So the filter below keeps every key, and the
    test `ids_follows_the_model` in `src/ids.rs` checks the order. -/
def ids.Ids.ids {V : Type} (m : ids.Ids V) : Result (alloc.vec.Vec time.EntityId) :=
  let l := (Std.ExtTreeMap.keys m).filterMap (fun k =>
    if h : k < 2 ^ UScalarTy.U32.numBits then some (UScalar.ofNatCore k h) else none)
  if h : l.length ≤ Usize.max then ok (alloc.vec.Vec.from l h) else fail .panic

/-- `Ids::len` is the number of ids in the map. -/
def ids.Ids.len {V : Type} (m : ids.Ids V) : Result Std.Usize :=
  if h : Std.ExtTreeMap.size m < 2 ^ UScalarTy.Usize.numBits then
    ok (UScalar.ofNatCore _ h)
  else fail .panic

/-! ## The type map of a link, and the derives of `EntityType` -/

/-- `Borrow` of a value as itself gives the value. -/
@[rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
def core.borrow.Borrow.Blanket.borrow {T : Type} (x : T) : Result T :=
  ok x

/-- The first entry whose key compares equal to `q`. -/
def btreeLookup {K V Q : Type} (bor : K → Result Q) (cmp : Q → Q → Result Ordering) :
    List (K × V) → Q → Result (Option V)
  | [], _ => ok none
  | (k, v) :: rest, q => do
    let kq ← bor k
    let o ← cmp kq q
    if o = .eq then ok (some v) else btreeLookup bor cmp rest q

/-- `BTreeMap::get` on the list model: the value of the entry with an
    equal key. A real map lists each key one time, in order, so the
    first equal key is the one key. The test
    `type_allowed_follows_the_model` in `src/fact.rs` checks this. -/
def alloc.collections.btree.map.BTreeMap.get
    {K : Type} {V : Type} {A : Type} {Q : Type}
    (_coreallocAllocatorCloneInst : core.alloc.AllocatorClone A)
    (coreborrowBorrowInst : core.borrow.Borrow K Q)
    (_corecmpOrdInst : core.cmp.Ord K) (corecmpOrdInst1 : core.cmp.Ord Q)
    (m : alloc.collections.btree.map.BTreeMap K V A) (q : Q) : Result (Option V) :=
  btreeLookup coreborrowBorrowInst.borrow corecmpOrdInst1.cmp m q

/-- `BTreeMap::is_empty`: the list has no entry. -/
def alloc.collections.btree.map.BTreeMap.is_empty
    {K : Type} {V : Type} {A : Type}
    (_coreallocAllocatorCloneInst : core.alloc.AllocatorClone A)
    (m : alloc.collections.btree.map.BTreeMap K V A) : Result Bool :=
  ok (List.isEmpty (m : List (K × V)))

/-- The place of a variant in the declaration. The derives of
    `EntityType` compare this number. -/
def etRank : entity.EntityType → Nat
  | .Person => 0
  | .Place => 1
  | .Thing => 2
  | .Faction => 3

/-- `EntityType != EntityType`, by the derive. -/
def entity.EntityType.Insts.CoreCmpPartialEqEntityType.ne
    (a b : entity.EntityType) : Result Bool :=
  ok (etRank a != etRank b)

/-- The derive of `Eq` checks nothing at run time. -/
def entity.EntityType.Insts.CoreCmpEq.assert_fields_are_eq
    (_ : entity.EntityType) : Result Unit :=
  ok ()

/-- `<`, `>`, and `>=` on `EntityType`, by the derive: the order of
    the declaration. -/
def entity.EntityType.Insts.CoreCmpPartialOrdEntityType.lt
    (a b : entity.EntityType) : Result Bool :=
  ok (decide (etRank a < etRank b))

def entity.EntityType.Insts.CoreCmpPartialOrdEntityType.gt
    (a b : entity.EntityType) : Result Bool :=
  ok (decide (etRank a > etRank b))

def entity.EntityType.Insts.CoreCmpPartialOrdEntityType.ge
    (a b : entity.EntityType) : Result Bool :=
  ok (decide (etRank a ≥ etRank b))

/-- `Ord::max` and `Ord::min`, as std defines them: on a tie, `max`
    gives the second value and `min` gives the first. -/
def entity.EntityType.Insts.CoreCmpOrd.max
    (a b : entity.EntityType) : Result entity.EntityType :=
  ok (if etRank a > etRank b then a else b)

def entity.EntityType.Insts.CoreCmpOrd.min
    (a b : entity.EntityType) : Result entity.EntityType :=
  ok (if etRank a > etRank b then b else a)

/-! ## The one query of the gate with a model body

`validate` translates in full, except `validate::queries::blank`.
`trim` is not in the Aeneas library, so the model states what
`trim().is_empty()` means: every char is Unicode `White_Space`, the
set of `char::is_whitespace`. The test `blank_follows_the_model` in
`src/validate.rs` checks the list below against the Rust code. -/

/-- The Unicode `White_Space` chars, as `char::is_whitespace` lists them. -/
def rustWhiteSpace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n ∧ n ≤ 0x0D) || n = 0x20 || n = 0x85 || n = 0xA0 || n = 0x1680 ||
  (0x2000 ≤ n ∧ n ≤ 0x200A) || n = 0x2028 || n = 0x2029 || n = 0x202F ||
  n = 0x205F || n = 0x3000

/-- [hourglass::validate::queries::blank]: a name with nothing in it
    but white space. -/
def validate.queries.blank (s : String) : Result Bool :=
  ok (s.toList.all rustWhiteSpace)
