-- The external types: the types that Aeneas does not translate.
--
-- Aeneas writes each one as an opaque axiom. This file gives each
-- one a definition, so the proofs use no axiom of the model. Read it
-- with FunsExternal.lean: the two files are the trusted part of the
-- proofs. extract.sh never overwrites this file.
module
public import Aeneas
public import Std.Data.ExtTreeMap
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.style.setOption false
set_option linter.style.longLine false

/-- The map in `FactRules::Linked`, from a holder type to its target
    types: the list of its entries in key order. The test
    `type_allowed_follows_the_model` in `src/fact.rs` checks the model. -/
@[rust_type "alloc::collections::btree::map::BTreeMap"]
def alloc.collections.btree.map.BTreeMap (K : Type) (V : Type) (_A : Type) : Type :=
  List (K × V)

/-- `Names<V>` in `src/names.rs`: a `BTreeMap<String, V>`.

    The model is the verified tree map of the Lean standard library,
    ordered by `compare` on `String`. Two facts make it faithful:

    1. A `BTreeMap` with one key set and one value per key behaves the
       same, whatever its inner tree shape. So two maps with the same
       entries are one map. `ExtTreeMap` holds exactly that law.
    2. Rust orders a `String` by its UTF-8 bytes, and Lean orders it by
       its code points. UTF-8 keeps the code point order, so the two
       orders agree. A test in `src/names.rs` checks this on random
       strings. -/
abbrev names.Names (V : Type) : Type := Std.ExtTreeMap String V compare

/-- `Ids<V>` in `src/ids.rs`: a `BTreeMap<EntityId, V>`.

    The model is the verified tree map of the Lean standard library,
    keyed by the number of the id. An `EntityId` is a `u32`, and the
    number of a `u32` keeps both its identity and its order, so the
    model orders the ids as Rust does. The tests in `src/ids.rs`
    check the laws of the model against the Rust code. -/
abbrev ids.Ids (V : Type) : Type := Std.ExtTreeMap Nat V compare

