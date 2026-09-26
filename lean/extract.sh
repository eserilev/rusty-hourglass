#!/usr/bin/env bash
# Translate the verified part of the crate to Lean with Charon and Aeneas.
#
# Set AENEAS to the root of an Aeneas checkout at the commit in
# lakefile.toml, with `make setup-charon` and `make` done. For example:
#   AENEAS=~/.cache/verif/aeneas lean/extract.sh
# The script writes lean/Hourglass/Types.lean and lean/Hourglass/Funs.lean.
# Never edit those two files by hand. Run this script again.
set -euo pipefail

: "${AENEAS:?set AENEAS to the root of an Aeneas checkout}"
here="$(cd "$(dirname "$0")" && pwd)"
crate="$(dirname "$here")"
work="$(mktemp -d "${XDG_CACHE_HOME:-$HOME/.cache}/hourglass-extract.XXXXXX")"
trap 'rm -rf "$work"' EXIT

# The roots of the translation are the functions with the mark
# `#[cfg_attr(charon, verify::start_from)]` in src/. Charon also
# translates everything a root calls. To verify one more function,
# put the mark on it. A name pattern is not enough: Charon cannot
# match one method of an inherent impl block.
#
# --duplicate-defaulted-methods: without it, Aeneas passes a whole
# PartialOrd instance where its Lean library takes one function, for
# example on `Tick < Tick`, and the Lean does not build.
args=(--preset=aeneas --duplicate-defaulted-methods --start-from-attribute)
# The serde derives and the Debug derives are not part of any law.
args+=(
  --exclude '{impl serde_core::ser::Serialize for _}'
  --exclude '{impl serde_core::de::Deserialize for _}'
  --exclude '{impl core::fmt::Debug for _}'
  --exclude '{impl core::hash::Hash for _}'
  # The name map is a model in Lean (Hourglass/TypesExternal.lean), so
  # Aeneas sees only the signatures of its operations.
  --opaque 'hourglass::names'
)

(cd "$crate" && RUSTFLAGS="--cfg charon" "$AENEAS/charon/bin/charon" cargo "${args[@]}" --dest-file "$work/hourglass.llbc")

"$AENEAS/bin/aeneas" -backend lean -split-files -loops-to-rec \
  -subdir Hourglass -dest "$work/out" "$work/hourglass.llbc"

mkdir -p "$here/Hourglass"
cp "$work/out/Hourglass/Types.lean" "$work/out/Hourglass/Funs.lean" "$here/Hourglass/"

# The external model: the std items the code calls. Aeneas writes a
# template of opaque declarations with no laws. The first run copies
# the template. After that, the model file is yours: the script never
# overwrites it, and it writes the new template beside it for a diff.
for f in TypesExternal FunsExternal; do
  src="$work/out/Hourglass/${f}_Template.lean"
  [ -f "$src" ] || continue
  if [ -f "$here/Hourglass/$f.lean" ]; then
    cp "$src" "$here/Hourglass/${f}_Template.lean"
    echo "note: compare Hourglass/${f}_Template.lean with Hourglass/$f.lean" >&2
  else
    cp "$src" "$here/Hourglass/$f.lean"
  fi
done
