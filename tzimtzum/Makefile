LEAN_NUM_THREADS ?= 12

.PHONY: build verify test clean

# Fast incremental build of the spec (default target).
build:
	LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) lake build Tzimtzum

# Full verification: CLEAN rebuild of the spec, every per-action check, the reachable
# soundness crown, per-transition results, and axiom audit. The clean rebuild is the point.
# NOTE: `lake clean` with no argument deletes the build directory of EVERY package in the
# workspace, mathlib included -- which throws away the downloaded cache and rebuilds it from
# source. Always name the package.
verify:
	lake clean tzimtzum
	LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) lake build Tzimtzum TzimtzumTest

test: verify

# Clean this package only (see the note on `verify`).
clean:
	lake clean tzimtzum
