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
