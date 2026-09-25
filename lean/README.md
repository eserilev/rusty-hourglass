# The Lean proofs

Aeneas translates the Rust code of the crate into pure Lean
functions. The theorems in `Hourglass/Laws.lean` are about those
functions. A theorem holds for every input, with no bound. Kani
checks the same laws in `src/proofs.rs`, but only up to its bounds.

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

## What you trust

1. **Charon and Aeneas.** A bug in the translation makes the Lean
   differ from the Rust.
2. **`Hourglass/FunsExternal.lean`.** Aeneas does not translate
   std. This file gives a body to the three std items that the
   core calls: `Option` equality, and `<` and `>=` on `Tick`. Read
   it before you trust a theorem. It is short.
3. **The three standard axioms of Lean.** `Hourglass/Trust.lean`
   pins the axioms of each theorem with `#guard_msgs`. A `sorry` or
   a new axiom fails the build.

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

### Rung 2: the record merge

Prove that `merge` is commutative, associative, and idempotent, for
every record size and every schema. This is the law behind the gold
that resurrects through a save.

The spike found that `merge`, `check`, `join_of`, `Record::get`, and
`Record::set` already translate. The only gap is std. `merge` calls
these std items:

- `BTreeMap`: `new`, `get`, `insert`, `remove`, `len`, `iter`, `keys`
- `BTreeSet`: `new`, `extend`, `into_iter`, `next`
- `Vec`: `extend`, `is_empty`
- `String`: `cmp`, `deref`, `to_string`
- `Option`: `and_then`, `filter`

The plan: put the maps behind one small wrapper type with about six
operations. Mark the operations opaque, and state the map laws in
Lean: `get` after `insert`, `get` on `empty`, and a walk in strictly
ascending key order. Test each law in Rust against the real
`BTreeMap` with proptest. Then the trusted model is about ten laws,
not twenty std items.

### Rung 3: the world

Prove that `replay` is deterministic, that `rewind` equals a replay
of the cut history, and that `propose` accepts only events that pass
`validate`. The code needs changes first. A full run of the crate
shows five groups of code that Aeneas does not translate yet:

| Group | Where | The fix |
|---|---|---|
| A `&'static str` label, and the text of a rejection | `EntityType::label`, `EventKind` label, `Direction::label`, `Shape::label`, `reject.rs` lines 221 and 326 | None. These are text, and no law reads them. Keep them out of the marks. |
| An iterator chain with a closure | `Entity::fact`, `Entity::location`, `World::contents`, `holders_of`, `targets_of`, `facts_linked_to`, `apply`, `memory_names` | Write each one as an explicit loop over the wrapper walk. |
| A closure that captures `&mut self` | `World::propose_all` | A loop that calls `propose`. |
| A return inside a nested loop | `verify::same_state`, `verify::sound` | Move the inner loop into a helper function that returns a flag. |
| A borrow shape that Aeneas does not support yet | `validate.rs` lines 96 to 112, 131, 132, 215, and 422 to 449; `memory::writes` | Read each one. Most are a `&mut` borrow held across a call. |

The serde derives do not block anything. The extraction excludes
them by pattern, with no change to the code.

## Two issues for upstream

1. Without `--duplicate-defaulted-methods`, Aeneas passes a whole
   `PartialOrd` instance to `core.cmp.PartialOrd.lt.default`, but
   the Lean library takes only the `partial_cmp` function. The
   generated Lean does not build. `Tick < Tick` shows it.
2. Several spots in rung 3 fail with "Internal error: please file
   an issue". File them with a minimal case when rung 3 starts.
