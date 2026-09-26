# The Lean proofs

Aeneas translates the Rust code of the crate into pure Lean
functions. The theorems in `Hourglass/Laws.lean`,
`Hourglass/Merge.lean`, and `Hourglass/World.lean` are about those
functions. A theorem holds
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

These laws hold for every `apply` and every `validate`. They are
about the discipline of the history, not about the rules inside
`apply` and `validate`. So those two functions stay opaque: Aeneas
sees only their types. `apply` receives only the entity map and the
vocabulary, so it cannot touch the history or the tick. The laws
rest on that signature.

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
   - The map inside `FactRules` and the entity map of the world. No
     law reads them, so their model is a plain list.
   - `Names<V>` (`src/names.rs`), the one map with a name for its
     key. Its model is `Std.ExtTreeMap String V compare`, the
     verified tree map of the Lean standard library. Each operation
     is the `ExtTreeMap` operation of the same name.
3. **The contract tests of the map.** The tests in `src/names.rs`
   check the laws of the map model against the real `BTreeMap` on
   random input. One test checks that Rust and Lean order strings
   the same way.
4. **The three standard axioms of Lean.** `Hourglass/Trust.lean`
   pins the axioms of each theorem with `#guard_msgs`. A `sorry` or
   a new axiom fails the build. The model files hold definitions
   only, with two exceptions: the crate functions `apply` and
   `validate`. They are axioms with no body, and only the rung 3
   pins name them. An axiom that only names a function of an
   inhabited type cannot make the logic inconsistent.

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

### Rung 4: the rules inside `apply` and `validate`

For example: one fact per slot, no cycle in `located_in`, and every
event in a history passes `validate` at its time. These laws read
the bodies of `apply` and `validate`, so the code needs changes
first. A full run of the crate shows five groups of code that Aeneas
does not translate yet:

| Group | Where | The fix |
|---|---|---|
| A `&'static str` label, and the text of a rejection | `EntityType::label`, `EventKind` label, `Direction::label`, `Shape::label`, `reject.rs` lines 221 and 326 | None. These are text, and no law reads them. Keep them out of the marks. |
| An iterator chain with a closure | `Entity::fact`, `Entity::location`, `World::contents`, `holders_of`, `targets_of`, `facts_linked_to`, `apply`, `memory_names` | Write each one as an explicit loop over the wrapper walk. |
| A closure that captures `&mut self` | `World::propose_all` | A loop that calls `propose`. |
| A return inside a nested loop | `verify::same_state`, `verify::sound` | Move the inner loop into a helper function that returns a flag. |
| A borrow shape that Aeneas does not support yet | `validate.rs` lines 96 to 112, 131, 132, 215, and 422 to 449; `memory::writes` | Read each one. Most are a `&mut` borrow held across a call. |

The entity map also needs a wrapper like `Names`, keyed by
`EntityId`.

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
