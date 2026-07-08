#!/usr/bin/env bash
# Regenerate the Lean model of argus-kernel via Charon + Aeneas (Phase B, 4.30 stack).
#
# Realigned toolchain (Phase B, 2026-05-29):
#   aeneas  1163128c  (origin/main, Lean backend rebased rc2 -> v4.30.0 stable)
#   charon  a0bd2aed  (v0.1.198; fixes the 43459f88 Iterator-trait ingest bug)
#   aeneas Lean lib   Lean v4.30.0 + mathlib v4.30.0 (matches kav/tzimtzum)
#   charon rust       nightly-2026-02-22  (+rustc-dev rust-src llvm-tools-preview)
#
# ENV RECIPE (must hold, or this fails — hard-won from the phase-0 spike):
#   1. opam: build deps live in the dedicated `aeneas` switch (OCaml 5.3.0). Activate it:
#        eval "$(opam env --switch=aeneas --set-switch)"
#      (opam itself is mise-managed: /Users/<you>/.local/share/mise/installs/opam/<ver>/opam)
#   2. RUSTUP_TOOLCHAIN: mise exports RUSTUP_TOOLCHAIN=1.93.0, which silently overrides
#      Charon's pinned nightly and breaks the charon driver. This script unsets it per-invocation
#      so charon/charon-cargo pick up charon/charon/rust-toolchain (nightly-2026-02-22).
#   3. macOS: use gmake (BSD make is rejected by the aeneas Makefile) when (re)building the tools.
#   4. The aeneas Std lib ships a `sorry` (Aeneas/Std/*Iter.lean) — a TCB note for #print axioms.
#
# Prereqs: tools/aeneas built (bin/aeneas) and Charon set up (gmake setup-charon && gmake build-bin-dir).
# Usage:   eval "$(opam env --switch=aeneas --set-switch)" && argus/scripts/charon-aeneas-extract.sh
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
AENEAS="$ROOT/tools/aeneas"
KERNEL="$ROOT/argus/crates/argus-kernel"
OUT="$ROOT/argus/formal-lean/ArgusLean/Generated"

# Charon's pinned nightly (read from its rust-toolchain so this never drifts from the pin).
CHARON_NIGHTLY="$(sed -n 's/^channel = "\(.*\)"/\1/p' "$AENEAS/charon/charon/rust-toolchain" 2>/dev/null | head -n1)"
CHARON_NIGHTLY="${CHARON_NIGHTLY:-nightly-2026-02-22}"

# Locate the charon binary (path varies: charon/bin or charon/target/release).
CHARON_BIN="$(find "$AENEAS/charon" -maxdepth 3 -type f -name charon -perm -u+x 2>/dev/null | head -n1)"
if [[ -z "${CHARON_BIN:-}" ]]; then
  echo "ERROR: charon binary not found under $AENEAS/charon — run 'gmake setup-charon && gmake build-bin-dir' first" >&2
  exit 1
fi
echo "charon: $CHARON_BIN"
echo "aeneas: $AENEAS/bin/aeneas"
echo "nightly: $CHARON_NIGHTLY"

mkdir -p "$OUT"

# 1. Rust -> LLBC (run inside the crate so Cargo metadata resolves; force charon's nightly).
( cd "$KERNEL" && env RUSTUP_TOOLCHAIN="$CHARON_NIGHTLY" "$CHARON_BIN" cargo --preset=aeneas )

# 2. Find the produced LLBC. The current charon writes it to the workspace root (argus/),
#    not under the crate — search both.
LLBC="$(find "$ROOT/argus" -maxdepth 2 -name '*.llbc' -newermt '-5 minutes' 2>/dev/null | head -n1)"
LLBC="${LLBC:-$(find "$ROOT/argus" -maxdepth 2 -name 'argus_kernel.llbc' 2>/dev/null | head -n1)}"
if [[ -z "${LLBC:-}" ]]; then
  echo "ERROR: no .llbc produced by charon" >&2
  exit 1
fi
echo "LLBC: $LLBC"

# 3. LLBC -> Lean.
"$AENEAS/bin/aeneas" -backend lean -dest "$OUT" "$LLBC"
echo "Generated Lean written to $OUT"
