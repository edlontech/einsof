LEAN_NUM_THREADS ?= 12

.PHONY: build verify test clean

# Fast incremental build of the spec (default target).
build:
	LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) lake build Tzimtzum

# Build the spec + all per-action VC checks + axiom audit.
verify:
	LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) lake build Tzimtzum TzimtzumTest

test: verify

clean:
	lake clean
