# Lean verification-stack upgrade (Task P0)

Task P0 moved the complete Kav → TzimtzumV3 → extracted Argus refinement pipeline from Lean 4.30
to the latest mutually compatible stable stack available on 2026-07-27. These versions are frozen
for the TzimtzumV4 campaign.

## Versions evaluated and selected

Lean 4.31 was evaluated as the intermediate stable line: current Aeneas upstream already built
against 4.31, but Kav's automation dependencies and mathlib had stable 4.32 releases. The selected
line is therefore Lean/mathlib 4.32.1, with the latest compatible stable 4.32.0 tags for packages
that did not publish a 4.32.1 tag. No release candidate or moving branch is used.

Release notes reviewed for the skipped stable line and selected feature line:

- [Lean 4.31.0](https://lean-lang.org/doc/reference/latest/releases/v4.31.0/)
- [Lean 4.32.0](https://lean-lang.org/doc/reference/latest/releases/v4.32.0/)

| Component | Declared pin | Resolved commit |
|---|---|---|
| Lean | `v4.32.1` | toolchain tag |
| mathlib | `v4.32.1` | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| Duper | `v4.32.0` | `0992bfade8392ca97ef0f3c547aec414b3b42075` |
| lean-auto | `v4.32.0` | `fcbce0f216e71516e88b784944636da4d28ee780` |
| REPL | `v4.32.0` | `68a3b3a059787a7db44fb1e6281e4a657efee470` |
| Aeneas | exact commit | `3a8586facab25b31bdb1e1f5f45acd60d1cc5ff0` |
| Charon | exact commit | `527ea8e3b5dcb52edd6aef0f7bc34cc09c11dd59` |
| Charon Rust | exact nightly | `nightly-2026-06-01` |

The tracked Lake manifests freeze the complete transitive graph. The Aeneas checkout is ignored,
so its exact Lean 4.32.1 compatibility delta is tracked as
`patches/aeneas-lean-v4.32.1.patch`; the extraction script verifies both clean source trees and the
exact patch, then clean-rebuilds the ignored extractor binaries before use.

## Compatibility adaptations

No TzimtzumV3 state, action, guard, invariant, or theorem statement changed. Required upgrade-only
repairs were:

- Aeneas meta modules: adopt Lean's public/meta module imports and the relocated BVDecide
  namespaces/configuration APIs.
- Aeneas tactics: adapt `simpGoal`'s optional result, async `TaskOrDone`, command-modifier
  elaboration, and a missing explicit result return exposed by 4.32 elaboration.
- Aeneas/mathlib APIs: use `NPow.toPow` and rename Aeneas Array/Vector lemmas that now collide with
  upstream declarations.
- Extracted model: regenerate with the frozen Aeneas/Charon pair. New extraction represents
  `PartialEq::ne` and scalar `Ord::min` through proved trait defaults; refinement bridges were
  adjusted to those equivalent generated terms.
- Lean proofs: remove rewrites/tactics made redundant by stronger 4.32 simplification and update
  two existential-normalization proofs. No project-local `sorry` was added.

## Compatibility evidence

The versions are mutually compatible because the following completed from clean build directories:

- `kav`: `lake exe cache get && lake build Kav KavTest`
- `tzimtzum`: `lake exe cache get && make verify` (all unchanged V3 VCs and axiom audits)
- patched Aeneas Lean backend: `lake exe cache get && lake build`
- `argus/formal-lean`: `lake exe cache get && lake build`, including `implementation_sound`
- Rust → Charon → Aeneas → Lean extraction, repeated with byte-identical generated output

`implementation_sound` gained no trust assumption. Its former per-identifier `PartialEq::ne`
axioms disappeared because the extractor now uses Aeneas's proved default method. The exact current
axiom closure is documented in `README.md` and contains no `sorryAx`.
