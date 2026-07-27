#!/usr/bin/env bash
# Regenerate the Lean model of argus-kernel via the frozen V4-campaign extractor stack.
#
# Frozen toolchain (Task P0, 2026-07-27):
#   aeneas  3a8586facab25b31bdb1e1f5f45acd60d1cc5ff0
#   charon  527ea8e3b5dcb52edd6aef0f7bc34cc09c11dd59 (Aeneas charon-pin)
#   aeneas Lean lib   Lean/mathlib v4.32.1 plus the tracked compatibility patch
#   charon rust       nightly-2026-06-01 (+rustc-dev rust-src llvm-tools-preview)
#
# Recreate tools/aeneas (the directory is intentionally gitignored):
#   git clone https://github.com/AeneasVerif/aeneas tools/aeneas
#   git -C tools/aeneas checkout 3a8586facab25b31bdb1e1f5f45acd60d1cc5ff0
#   git -C tools/aeneas apply --unidiff-zero ../../argus/formal-lean/patches/aeneas-lean-v4.32.1.patch
#   (cd tools/aeneas && env -u RUSTUP_TOOLCHAIN gmake setup-charon)
#   (cd tools/aeneas && eval "$(opam env --switch=aeneas --set-switch)" && gmake build-bin-dir)
#
# ENV RECIPE (must hold, or this fails):
#   1. opam: build deps live in the dedicated `aeneas` switch (OCaml 5.3.0). Activate it:
#        eval "$(opam env --switch=aeneas --set-switch)"
#      (opam itself is mise-managed: /Users/<you>/.local/share/mise/installs/opam/<ver>/opam)
#   2. RUSTUP_TOOLCHAIN: mise exports RUSTUP_TOOLCHAIN=1.93.0, which silently overrides
#      Charon's pinned nightly and breaks the charon driver. This script sets it per-invocation
#      to the verified charon/charon/rust-toolchain value (`nightly-2026-06-01`).
#   3. macOS: use gmake (BSD make is rejected by the aeneas Makefile) when (re)building the tools.
#   4. Aeneas Std still contains documented `sorry`s, though the current
#      `implementation_sound` dependency closure does not include `sorryAx`.
#
# Prereqs: the exact patched tools/aeneas stack above and its OCaml dependencies. The script
# clean-rebuilds both extractor binaries before use so ignored/stale artifacts cannot bypass pins.
# Usage:   eval "$(opam env --switch=aeneas --set-switch)" && argus/scripts/charon-aeneas-extract.sh
set -euo pipefail

# Upstream build recipes copy from these default directories. Inherited overrides could clean and
# build elsewhere while leaving stale ignored artifacts at the hard-coded copy locations.
unset CARGO_TARGET_DIR DUNE_BUILD_DIR

ROOT="$(git rev-parse --show-toplevel)"
AENEAS="$ROOT/tools/aeneas"
KERNEL="$ROOT/argus/crates/argus-kernel"
OUT="$ROOT/argus/formal-lean/ArgusLean/Generated"
PATCH="$ROOT/argus/formal-lean/patches/aeneas-lean-v4.32.1.patch"
EXPECTED_AENEAS="3a8586facab25b31bdb1e1f5f45acd60d1cc5ff0"
EXPECTED_CHARON="527ea8e3b5dcb52edd6aef0f7bc34cc09c11dd59"
EXPECTED_NIGHTLY="nightly-2026-06-01"

[[ "$(git -C "$AENEAS" rev-parse HEAD 2>/dev/null)" == "$EXPECTED_AENEAS" ]] || {
  echo "ERROR: tools/aeneas is not at $EXPECTED_AENEAS" >&2
  exit 1
}
[[ "$(git -C "$AENEAS/charon" rev-parse HEAD 2>/dev/null)" == "$EXPECTED_CHARON" ]] || {
  echo "ERROR: tools/aeneas/charon is not at $EXPECTED_CHARON" >&2
  exit 1
}
cmp -s "$PATCH" <(git -C "$AENEAS" diff HEAD --binary --unified=0 -- backends/lean) || {
  echo "ERROR: tools/aeneas does not exactly match the tracked Lean 4.32.1 patch" >&2
  exit 1
}
git -C "$AENEAS" diff --quiet HEAD -- . ':(exclude)backends/lean' || {
  echo "ERROR: tools/aeneas has tracked changes outside the compatibility patch" >&2
  exit 1
}
[[ -z "$(git -C "$AENEAS" ls-files --others --exclude-standard)" ]] || {
  echo "ERROR: tools/aeneas has untracked, non-ignored files" >&2
  exit 1
}
[[ -z "$(git -C "$AENEAS/charon" status --porcelain --untracked-files=all)" ]] || {
  echo "ERROR: tools/aeneas/charon is not clean" >&2
  exit 1
}

# Charon's nightly is part of the frozen pin; missing or different values are fatal.
CHARON_NIGHTLY="$(sed -n 's/^channel = "\(.*\)"/\1/p' "$AENEAS/charon/charon/rust-toolchain" 2>/dev/null | head -n1 || true)"
[[ "$CHARON_NIGHTLY" == "$EXPECTED_NIGHTLY" ]] || {
  echo "ERROR: Charon Rust toolchain is '$CHARON_NIGHTLY', expected '$EXPECTED_NIGHTLY'" >&2
  exit 1
}

# Build from the verified trees. Both output directories are ignored, so accepting existing
# executables would allow stale or locally substituted binaries to bypass the source pins.
echo "clean-rebuilding frozen Charon/Aeneas binaries"
rm -f "$AENEAS/charon/bin/charon" "$AENEAS/charon/charon/target/release/charon" \
  "$AENEAS/bin/aeneas" "$AENEAS/src/_build/default/main.exe"
( cd "$AENEAS/charon/charon" && env RUSTUP_TOOLCHAIN="$CHARON_NIGHTLY" cargo clean )
( cd "$AENEAS/charon" && env RUSTUP_TOOLCHAIN="$CHARON_NIGHTLY" make build-charon-rust )
( cd "$AENEAS/src" && dune clean )
( cd "$AENEAS" && gmake build-bin-dir )

# Formatting is part of Charon's build; confirm neither build mutated the frozen inputs.
cmp -s "$PATCH" <(git -C "$AENEAS" diff HEAD --binary --unified=0 -- backends/lean) || {
  echo "ERROR: rebuilding changed the patched Aeneas source tree" >&2
  exit 1
}
git -C "$AENEAS" diff --quiet HEAD -- . ':(exclude)backends/lean' || {
  echo "ERROR: rebuilding changed Aeneas sources outside the compatibility patch" >&2
  exit 1
}
[[ -z "$(git -C "$AENEAS/charon" status --porcelain --untracked-files=all)" ]] || {
  echo "ERROR: rebuilding changed the frozen Charon source tree" >&2
  exit 1
}

CHARON_BIN="$AENEAS/charon/bin/charon"
AENEAS_BIN="$AENEAS/bin/aeneas"
[[ -x "$CHARON_BIN" && -x "$AENEAS_BIN" ]] || {
  echo "ERROR: clean extractor build did not produce the expected binaries" >&2
  exit 1
}
echo "charon: $CHARON_BIN"
echo "aeneas: $AENEAS_BIN"
echo "nightly: $CHARON_NIGHTLY"

mkdir -p "$OUT"

# 1. Rust -> LLBC. Remove the one exact expected output first: accepting an existing file or
# scanning for a recent arbitrary LLBC would allow stale/concurrent artifacts into the model.
LLBC="$ROOT/argus/argus_kernel.llbc"
rm -f "$LLBC"
( cd "$KERNEL" && env RUSTUP_TOOLCHAIN="$CHARON_NIGHTLY" "$CHARON_BIN" cargo --preset=aeneas )
[[ -f "$LLBC" ]] || {
  echo "ERROR: Charon did not produce $LLBC" >&2
  exit 1
}
echo "LLBC: $LLBC"

# 2. LLBC -> Lean. Require a freshly produced exact module, never a stale tracked output.
LEAN_OUT="$OUT/ArgusKernel.lean"
rm -f "$LEAN_OUT"
"$AENEAS_BIN" -backend lean -dest "$OUT" "$LLBC"
[[ -f "$LEAN_OUT" ]] || {
  echo "ERROR: Aeneas did not produce $LEAN_OUT" >&2
  exit 1
}
echo "Generated Lean written to $LEAN_OUT"
