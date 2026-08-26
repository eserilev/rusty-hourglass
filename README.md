# hourglass

A world that remembers. The crate holds the memory record: a
value, a declared merge direction, and a merge that always picks
the right side.

## The shape

Rows in: memory records with a declared direction — up for a best
score, down for a fastest time, last-write for a name. A checked
record set out, or every reason at once, in the hourglass
rejection shape that gave the doctrine its name.

## The laws

- Every record declares its direction. A merge with no declared
  direction refuses; a hardcoded max is the bug this crate exists
  to kill (spent gold that resurrects on load).
- A merge is idempotent and order-blind for up and down records.
- Whole numbers only.

## The seams

The server half of the progress seam consumes the record set. The
2D and 3D save paths are the target consumers.

## Testing

`cargo test -p hourglass` — 60 tests. `cargo kani` inside the
crate — ten proof harnesses.

The truth about scope and status lives in the specs at the repo
root; start at `spec/README.md`.
