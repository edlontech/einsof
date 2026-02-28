#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
KERNEL_DIR="$REPO_ROOT/crates/argus-kernel"
KERNEL_SRC="$KERNEL_DIR/src"
EXTRACTED_DIR="$REPO_ROOT/formal/extracted"
FORMAL_DIR="$REPO_ROOT/formal"
NIGHTLY="nightly-2024-12-07"

EXPECTED_MODULES=(
    background capability error event kernel state traits transitions types
)

step() { printf '\n==> %s\n' "$1"; }

step "Extracting Rocq from argus-kernel (cargo +$NIGHTLY rocq-of-rust)"
cd "$KERNEL_DIR"
# Extraction succeeds despite edition 2024 let-chain warnings.
# rocq-of-rust exits non-zero due to those warnings, so we don't fail on it.
cargo "+$NIGHTLY" rocq-of-rust 2>&1 || true

missing=()
for mod in "${EXPECTED_MODULES[@]}"; do
    if [[ ! -f "$KERNEL_SRC/$mod.v" ]]; then
        missing+=("$mod.v")
    fi
done

if [[ ${#missing[@]} -gt 0 ]]; then
    echo "ERROR: extraction failed -- missing files: ${missing[*]}"
    exit 1
fi
echo "Extracted ${#EXPECTED_MODULES[@]} modules."

step "Moving extracted files to $EXTRACTED_DIR"
mkdir -p "$EXTRACTED_DIR"
for mod in "${EXPECTED_MODULES[@]}"; do
    mv -f "$KERNEL_SRC/$mod.v" "$EXTRACTED_DIR/$mod.v"
done
echo "Moved ${#EXPECTED_MODULES[@]} files."

step "Building formal proofs (Rocq)"
cd "$FORMAL_DIR"
eval "$(opam env --switch=rocq-of-rust 2>/dev/null)" || true
make clean 2>/dev/null || true
make

step "All done"
echo "Extraction: ${#EXPECTED_MODULES[@]} modules in $EXTRACTED_DIR"
echo "Proofs:     $(grep -c '\.v' _CoqProject) files compiled successfully"
