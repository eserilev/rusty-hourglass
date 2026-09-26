# The Lean proofs

Aeneas translates the Rust code of the crate into pure Lean
functions. The theorems in `Hourglass/Laws.lean`,
`Hourglass/Merge.lean`, `Hourglass/World.lean`,
`Hourglass/Apply.lean`, `Hourglass/Gate.lean`,
`Hourglass/Direction.lean`, `Hourglass/Counts.lean`, and
`Hourglass/Cycle.lean` are about those functions. A theorem holds
for every input, with no bound. Kani checks the rung 1 laws in
`src/proofs.rs`, but only up to its bounds.

The Lean is generated from the Rust, so it does not drift from the
Rust. After a change to a marked function, run the extraction
again. If a law breaks, the build fails.

## What is proved: rung 1, the scalar core

| Theorem | The law | Kani twin |
|---|---|---|
| `join_comm` | The join of two numbers is the same in both orders. | `the_join_answers_the_same_either_way` |
| `join_assoc` | The grouping of three joins does not change the answer. | `the_join_ignores_the_grouping` |
| `join_idem` | The join of a number with itself is that number. | `the_join_of_one_record_with_itself_is_that_record` |
| `join_never_backward` | The join is at or past both sides, in the direction of the name. | `the_join_never_moves_backward` |
| `join_total` | The join never panics, for every join and every pair of values. | none |
| `join_stays_in_band` | Two numbers in a band join to a number in the same band. | `the_join_of_two_numbers_in_a_band_stays_in_the_band` |
| `clamp_lands` | The clamp lands in the band, and a second clamp moves nothing. | `a_number_lands_inside_its_band` |
| `wider_band_holds` | A wider band holds every number of the old band. | `a_wider_band_holds_every_old_number` |
| `allows_chain` | Two allowed writes in a row keep the order of the direction. | `a_write_the_direction_allows_keeps_the_order` |
| `one_is_at_most_one` | `One` is `AtMost(1)`. | `one_is_at_most_one` |
| `span_law` | A span holds its start and not its end. | `a_span_holds_its_start_and_not_its_end` |

Most theorems state the exact `ok` answer. So they also prove that
the function does not panic on those inputs.

## What is proved: rung 2, the record merge

These laws hold for records of any size and for any schema. Before
rung 2, a seeded sweep in `tests/laws.rs` checked them on random
records only. The sweep stays as a second check.

| Theorem | The law |
|---|---|
| `merge_comm` | Two records merge to the same record in either order. |
| `merge_assoc` | Three records merge to the same record, whichever two merge first. |
| `merge_self` | A merge of a record with itself gives the same record, so a merge that runs twice answers what it answered once. |
| `merge_empty` | A merge with an empty record gives the other record. |
| `merge_spec` | When both records fit the schema, the merge answers the join of each name. When one record does not fit, the merge refuses. |
| `check_spec` | `check` finds no fault exactly when every name of the record fits the schema. |
| `mergeRec_fits` | A merge of two records that fit gives a record that fits. |

The laws have three conditions:

1. **The records fit the schema** (`fits`). This is what `check`
   finds, by `check_spec`. `merge_comm` needs no such condition: it
   also covers two records that the merge refuses.
2. **The records hold no false flag** (`wf`). `Record::set` and the
   read from JSON keep this.
3. **The two records together hold at most `usize::MAX` names.** A
   larger record does not fit in memory.

## What is proved: rung 3, the world and its history

| Theorem | The law |
|---|---|
| `replay_is_the_world` | A world that commits built from an empty world is exactly the replay of its own history: the same entities, the same history, and the same tick. |
| `rewind_is_exact` | A rewind to the last event of an earlier world gives that world back, as if the later events never happened. |
| `propose_ok` | `propose` lands an event only when `validate` finds no fault, and then it is exactly `commit`. |
| `propose_err` | A refused proposal changes nothing, and it gives the faults that `validate` found. |
| `reach_propose` | So a world that any mix of proposals and commits built also replays exactly. |
| `replay_one_of_commit` | One step of replay on the event of a commit gives the world of that commit. |

`apply` receives only the entity map and
the vocabulary, so it cannot touch the history or the tick.

## What is proved: rung 4a, the rules inside `apply`

| Theorem | The law |
|---|---|
| `apply_one_fact_per_slot` | If no entity holds two facts in one slot, then after `apply` still none does. A slot is a name and a target. |
| `apply_one_target` | If each name that allows one target at a time holds at most one fact on each entity, then after `apply` this still holds. |
| `apply_keeps_ids` | `apply` never removes an entity. A destroyed entity stays, with its span closed. |
| `every_world_one_fact_per_slot` | So no world that commits and proposals build from an empty world holds two facts in one slot. |
| `every_world_one_target` | So in every such world, an entity holds at most one fact of a single-target name. For example, it sits in one place at a time. |
| `entities_never_vanish` | An entity of a world stays in every world that later commits and proposals build from it. |

These laws hold with or without `validate`. They are about `apply`
alone.

## What is proved: rung 4b, the rules inside `validate`

| Theorem | The law |
|---|---|
| `every_proposed_world_in_band` | In every world that proposals build from an empty world, every fact carries a declared name, a flag holds no number, and a number sits inside the band of its name. |
| `validate_clean` | A gate with no fault passes only a clean event: a start names a declared fact with a value that fits its shape, and an update names a declared number fact with a new value in its band. |
| `start_clean` and `update_clean` | The same, for each branch of the gate. |
| `apply_in_band` | `apply` keeps every value in its band, for a clean event. |
| `reachP_reach` | A world that proposals build is also a world that commits build. So the laws of rungs 3 and 4a hold for it too. |

`validate` translates in full. The one exception is `blank`, the test
for a name with only white space. Aeneas has no `trim`, so the model
gives `blank` a body (see "What you trust"). Each fault only adds to
the list. So "no fault at the end" means "no band fault".

## What is proved: rung 5, the direction law

| Theorem | The law |
|---|---|
| `up_never_falls` | In a world that proposals build from an empty world, a fact of an `Up` name stays in its slot in every later world, and its number never falls. For example, a best depth never falls, and an unlock is never lost. |
| `apply_up` | One clean event never lowers and never ends a fact of an `Up` name. |
| `validate_dir` | A gate with no fault passes only an event that keeps the direction. A start does not go back from the value it meets, an update replaces the value the world holds and does not go back from it, and a fact ends only when its direction allows an end. |
| `start_dir`, `update_dir`, and `end_dir` | The same, for each branch of the gate. |

The law covers every `Up` name that is not single-target. A
single-target name moves its fact to a new target, so the fact
leaves its old slot on purpose.

## What is proved: rung 6, the count laws

A linked name has two counts: the holders of one target, and the
targets of one holder.

| Theorem | The law |
|---|---|
| `every_proposed_world_holders` | In a world that proposals build from an empty world, a name with a limit of holders has at most that many holders of each target. |
| `apply_holders` | One event with a clean holder check keeps that limit. |
| `every_proposed_world_targets` | In a world that proposals build from an empty world, a name with a limit of targets above one holds at most that many facts on each entity. A fact carries a target exactly when its name takes one. |
| `apply_targets` | One event with a clean target check keeps that limit. |
| `apply_all_facts` | `apply` keeps each property that reads only the name and the target of a fact. |
| `apply_keyId` | `apply` keeps the key of each entity equal to its id. The holder law needs this, because the gate counts the holders by id. |

A limit of one target is the single-target law of rung 4a. The
holder check and the target check compare `len >= limit`, with no
add, so the Rust code has no overflow at the limit.

## What is proved: rung 7, no place inside itself

| Theorem | The law |
|---|---|
| `every_proposed_world_acyclic` | In a world that proposals build from an empty world, a walk up the `located_in` chain of one step or more never comes back to its start. |
| `no_place_inside_itself` | The same law as a relation: no entity sits inside itself through any chain of places. |
| `apply_acyc` | One event with a clean gate closes no ring. |
| `acyc_link` | A new step from `who` to `tgt` closes no ring when no walk from `tgt` meets `who`. |
| `walk_le_size` | In a world with no ring, a walk of `j` steps passes `j` different entities. So `j` is at most the number of entities. |
| `start_cycle_clean` | A start of `located_in` with no fault has a target whose walk never meets the entity, for every walk up to the number of entities. |
| `loc_test` | The name test of the gate and of `location` says `true` exactly for `located_in`. |

The law holds for a vocabulary that declares `located_in` with one
target, as `FactVocabulary::new` does. `vocabulary_sound` refuses any
other rules for the name.

## What you trust

1. **Charon and Aeneas.** A bug in the translation makes the Lean
   differ from the Rust.
2. **`Hourglass/FunsExternal.lean` and
   `Hourglass/TypesExternal.lean`.** Aeneas does not translate std.
   These files give a body to each std item that the verified code
   uses. Read them before you trust a theorem. They are short.
   - `Option` equality and clone, `<`, `>=`, and `>` on `Tick`,
     `String::clone`, `Vec::is_empty`, `Vec::truncate`,
     `Vec::default`, and `std::mem::take`.
   - `String` equality and `Vec::remove`.
   - `String` as `&str`, and `str` equality. The model of a `str` is
     its UTF-8 bytes, and the compare is on the bytes, as in Rust.
   - The type map inside `FactRules`. Its model is the list of its
     entries in key order, and `get` finds the first equal key.
   - The derives of `EntityType`: the compares follow the order of
     the declaration.
   - `blank`: every char is Unicode `White_Space`, the set of
     `char::is_whitespace`.
   - `Ids<V>` (`src/ids.rs`), the entity map of the world. Its model
     is `Std.ExtTreeMap Nat V compare`, keyed by the number of the
     id.
   - `Names<V>` (`src/names.rs`), the one map with a name for its
     key. Its model is `Std.ExtTreeMap String V compare`, the
     verified tree map of the Lean standard library. Each operation
     is the `ExtTreeMap` operation of the same name.
3. **The contract tests of the models.** The tests in
   `src/names.rs`, `src/ids.rs`, and `src/fact.rs` check the laws of
   each map model against the real `BTreeMap` on random input. One
   test checks that Rust and Lean order strings the same way. The
   tests in `src/validate.rs` check the model of `blank`: one walks
   every char, and one checks random names.
4. **The three standard axioms of Lean.** `Hourglass/Trust.lean`
   pins the axioms of each theorem with `#guard_msgs`. A `sorry` or
   a new axiom fails the build. The model files hold definitions
   only, and no law depends on an axiom of the crate. Every pin
   names exactly `propext`, `Classical.choice`, and `Quot.sound`.

## How to run

The tools are pinned to Aeneas commit `fd27c97` (see
`lakefile.toml`). Lean is `v4.31.0`, from `lean-toolchain`.

1. Install opam with OCaml 5, and install the packages that the
   Aeneas README lists.
2. Clone Aeneas and check out the pinned commit.
3. In the Aeneas directory, run `make setup-charon`, and then run
   `make` inside the opam environment.
4. Translate the crate:
   `AENEAS=<aeneas dir> lean/extract.sh`
5. Check the proofs: `cd lean && lake exe cache get && lake build`.

CI (`.github/workflows/ci.yml`) runs all of this on each push. Its
`extract` job fails when the committed Lean differs from the Lean
that Aeneas makes from the current Rust. The extraction also fails
when an item of the Aeneas template has no entry in the model.

The extraction writes `Hourglass/Types.lean` and
`Hourglass/Funs.lean`. Never edit these two files by hand. The
extraction never overwrites `Hourglass/FunsExternal.lean`. When
Aeneas needs a new std item, it writes
`Hourglass/FunsExternal_Template.lean`. Compare that file with the
model, and add a body for each new item.

## How to verify one more function

Put this mark on the function:

```rust
#[cfg_attr(charon, verify::start_from)]
pub fn holds(&self, n: i64) -> bool {
```

The extraction translates each marked function and everything it
calls. The mark exists only under `--cfg charon`, so a normal build
never sees it. A name pattern in the script is not enough: Charon
cannot select one method of an inherent impl block.

## The next rungs

### Rung 2: the record merge (BUILT)

Three facts about rung 2 help the next rungs:

1. **A name map goes through `Names<V>`.** The verified code looks a
   name up by `&String`, because Aeneas models `&str` as bytes. So
   `Names` has `get_key` and `remove_key` next to `get` and `remove`,
   and the contract tests check that each pair agrees.
2. **A loop walks a `Vec` of keys by index.** Aeneas translates this
   form into a recursive function. `step*` proves its loop lemma in
   a few lines.
3. **Each function gets a pure mirror first.** For example,
   `merge_name_eq` says that `merge_name` answers `stepOut`. The laws
   are about the mirrors, so they need no monad.

### Rung 3: the world (BUILT)

Two Rust changes made the laws possible:

1. **`apply` receives the entity map, not the world.** Before, `fold`
   took `&mut self`. The proof then had no way to rule out a change
   to the history by an opaque `fold`.
2. **A local never takes the name of a module.** Aeneas writes one
   name for the local `event` and the module `event`. The Lean then
   breaks. `commit` and `replay` use `ev` and `out`.

### Rung 4a: the rules inside `apply` (BUILT)

`apply` now translates in full. Three Rust changes made that
possible, with the same behavior:

1. The entity map is `Ids<V>`, a wrapper like `Names`.
2. `retain` is an index loop with `Vec::remove`, which keeps the
   order and copies nothing. `iter_mut().find` is an index loop.
3. `get_mut` is `take`, a change, and `insert`.

### Rung 4b: the rules inside `validate` (BUILT: the band law)

Three Rust changes made `validate` translate, with the same faults in
the same order:

1. The helpers take the name as `&String`, and the locals avoid the
   module names: the world is `w`, and the entity is `who`.
2. The world queries moved into `validate::queries`. A query answers
   a value and never receives the list of faults. `type_faults`
   answers its own list, and `push_all` adds it in the same place as
   before.
3. `Ids::get` has a model.

### Rung 5: the world queries (the direction law is BUILT)

The slot queries `slot_value` and `held_for_start` now translate as
index loops. So the direction law reads their real answers.

### Rung 6: the count check (BUILT)

The count check `counts_fit` translates. `holders_except` walks the
ids of the world with `Ids::ids`, and `targets_except` walks the
facts of the holder. Both are index loops. `Ids::ids` has a model and
a proptest.

### Rung 7: the ring check (BUILT)

The ring check `would_cycle` translates, and the proof found a bug in
it. The old walk stopped after 1024 hops and answered "no ring". So
the gate let a ring through when the chain held more than 1024
places. The referee `verify` had the same cap, and it called a sound
chain of that length unsound. The test
`a_ring_longer_than_any_cap_is_refused` holds both cases.

The new walk has no cap and no set. It walks at most `len` hops. In a
world with no ring, a walk that meets the entity meets it within
`len` hops (`walk_le_size`). `Entity::location` is an index loop.
`is_located_in` compares the bytes of the name with the byte array
`LOCATED_IN_BYTES`. Aeneas writes a `&str` constant with a proof by
native code, and a byte array needs no such proof. The kernel checks
that the array holds the bytes of `located_in` (`located_bytes`).

### Rung 8: the last queries (BUILT)

The type check `types_fit` and the history walk `ever_ended`
translate. `ever_ended` is an index loop on `EventHistory`, and
`type_allowed` reads the type map with `get` and `is_empty`. `blank`
keeps a model body and two contract tests. No law of the gate
depends on an axiom of the crate now.

What waits: no law reads the remaining code yet.

| Group | Where | The fix |
|---|---|---|
| A `&'static str` label, and the text of a rejection | `EntityType::label`, `EventKind` label, `Direction::label`, `Shape::label`, `reject.rs` lines 221 and 326 | None. These are text, and no law reads them. Keep them out of the marks. |
| An iterator chain with a closure | `Entity::fact`, `World::contents`, `holders_of`, `targets_of`, `facts_linked_to`, `memory_names` | Write each one as an explicit loop over the wrapper walk. |
| A closure that captures `&mut self` | `World::propose_all` | A loop that calls `propose`. |
| A return inside a nested loop | `verify::same_state`, `verify::sound` | Move the inner loop into a helper function that returns a flag. |

## Known Aeneas limits

Each limit has a workaround in the code. Keep the workarounds.

1. **`PartialOrd` default methods.** Without
   `--duplicate-defaulted-methods`, the generated Lean for
   `Tick < Tick` does not build. `extract.sh` sets the flag.
2. **A local with the name of a module.** A local named `event` hides
   the module `event` in the generated Lean. Name locals `ev`, `out`,
   and the like.
3. **An `if` in a loop that holds a borrow.** Aeneas stops with
   "Could not match the contexts". Move the loop body into a method.
   `World::replay_one` shows the form.
4. **Internal errors.** Some spots of the rung 4 map stop Aeneas
   with an internal error. Rewrite the spot in a simpler form.
