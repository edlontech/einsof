# argus-kernel Lean refinement (`formal-lean`)

Mechanically extracted Lean model of the Rust `argus-kernel`, refined against the pure-Lean
TzimtzumV4 Kav specification. The end-to-end theorem is:

```lean
ArgusLean.Refinement.implementation_sound
```

For every reachable state of the extracted kernel, modulo the explicit assumptions below, the
theorem produces a related TzimtzumV4 state satisfying `Tzimtzum.allInv`: all **32 invariants** over
the complete **12-action** V4 system.

The Rust kernel is translated by Charon and Aeneas. The pinned extraction script
[`../scripts/charon-aeneas-extract.sh`](../scripts/charon-aeneas-extract.sh) produces
`ArgusLean/Generated/ArgusKernel.lean`; generated Lean is never hand-edited.

## Build

```bash
lake build              # complete extracted model + V4 refinement + implementation_sound
lake build ArgusChecks  # opt-in Plausible collection-model checks
```

Lean 4.32.1 is pinned by `lean-toolchain`. After a toolchain change, run
`lake exe cache get` first.

### Frozen extraction stack

| Component | Pin |
|---|---|
| Lean / mathlib | `v4.32.1` |
| lean-auto / Duper | `v4.32.0` |
| REPL | `v4.32.0` |
| Aeneas | `3a8586facab25b31bdb1e1f5f45acd60d1cc5ff0` |
| Charon | `527ea8e3b5dcb52edd6aef0f7bc34cc09c11dd59` |
| Charon Rust | `nightly-2026-06-01` |

The compatibility review, patches, and clean-build evidence are in
[`UPGRADE-4.32.md`](UPGRADE-4.32.md). Recreate the intentionally ignored extractor checkout from the
repository root with:

```bash
git clone https://github.com/AeneasVerif/aeneas tools/aeneas
git -C tools/aeneas checkout 3a8586facab25b31bdb1e1f5f45acd60d1cc5ff0
git -C tools/aeneas apply --unidiff-zero ../../argus/formal-lean/patches/aeneas-lean-v4.32.1.patch
(cd tools/aeneas && env -u RUSTUP_TOOLCHAIN gmake setup-charon)
(cd tools/aeneas && eval "$(opam env --switch=aeneas --set-switch)" && gmake build-bin-dir)
```

The extraction script rejects source/pin/patch mismatches and clean-rebuilds the ignored extractor
binaries before use.

## Verified action surface

`KernelCmd`, `kernelStep`, `AbsStep`, and `step_refines` cover exactly these twelve transitions:

1. `register_tool`
2. `unregister_tool`
3. `delegate`
4. `grant_capability`
5. `grant_crossing`
6. `revoke`
7. `cascade_revoke`
8. `ingest`
9. `begin_invocation`
10. `authorize_inspected`
11. `settle_invocation`
12. `cross_output`

Each successful extracted transition maps to the corresponding single abstract action. Transparent
internal action parameters select disposition/verdict, live challenge scope, settlement fields, or
crossing branch; they do not widen a command to another action.

## Module map

```text
ArgusLean.lean
ArgusLean/
  Generated/ArgusKernel.lean        Charon/Aeneas output; DO NOT EDIT
  Refinement/
    Bridging/
      Collections.lean              VecMap/VecSet and extracted opaque-operation specs
      StateRelation.lean            V4 record/enum/state correspondences
      FlowBridging.lean             V4 flow/integrity gate bridges
      FlowOracle.lean               extracted read/loop specifications
    PlausibleChecks.lean            opt-in finite collection-model checks
    Unified/
      Relation.lean                 canonical V4 relation `R`; `AuAgree`/`EgressAgree`
      ViewCoincidence.lean          canonical-view lemmas
      NodupPreservation.lean        seven VecMap key-uniqueness fences
      Bridges.lean                  shared `R` projection helpers
      Preservation/                 12 action proofs plus shared `ClearAgent`
      InitRefinement.lean           V4 initial-state refinement
      Bundle.lean                   12-command dispatch and `step_refines`
      Soundness.lean                forward simulation and `implementation_sound`
```

Layering is strict: `Generated → Bridging → Unified`.

## What `implementation_sound` proves

For any governed background `bg`, fixed snapshot interpretation `snapRel`, fixed egress
interpretation `egRel`, fixed authorizer interpretation `auRel`, and reachable extracted state `c`:

```lean
∃ a, R c bg a ∧ Tzimtzum.allInv a
```

The proof composes:

1. `init_refines` for the extracted initial state;
2. `step_refines` for all twelve successful transitions;
3. abstract reachability in `Tzimtzum.system`; and
4. `Tzimtzum.kav_soundP` for the 32-invariant V4 bundle.

It verifies the extracted semantic model, not the hand-written Rust text directly. Charon/Aeneas are
trusted to translate that text faithfully. It also does not verify the external SPIFFE/STS mesh,
adapter, persistence, authenticated input construction, attestation truth, or event-store behavior.

## Explicit hypotheses

`implementation_sound` has exactly two caller-supplied assumption bundles.

### `CapacityOK`

`CapacityOK` states:

- concrete `AgentId.root` equals the governed `BackgroundTheory.root_agent` at initialization;
- the exact collection-capacity premises for the branch that successfully fires;
- the fixed per-invocation abstract snapshot predicts the concrete frozen snapshot at
  `begin_invocation`; and
- `grant_crossing n` satisfies the explicit abstract-`Nat`/Rust-`u32` boundary `n < 2^32`.

The crossing premises remain branch-specific: crossing-id capacity is unconditional; endorsed label,
evidence, and grant capacities require `endorsedOK`; unendorsed copy capacities require the
release-unendorsed branch. Settlement likewise separates ambiguous pending reinsertion,
non-ambiguous label absorption, and optional resolution-evidence consumption.

These are premises only for successful commands from reachable related states. They are not hidden in
the definition of concrete reachability.

### `OracleFidelity`

`OracleFidelity` contains only the two begin-time values lifted to the unverified driver:

- the authorizer verdict agrees with `auRel inv`; and
- the attested egress `VecSet` agrees extensionally with `egRel inv`.

Inspection, quarantine resolution, and crossing conformance are explicit scoped one-use attestation
data. The kernel checks their scope and consumption; there are no V3 content-gate, conformance, or
return-conformance oracle assumptions.

## Trust base

`#print axioms ArgusLean.Refinement.implementation_sound` reports:

- standard Lean axioms: `propext`, `Classical.choice`, `Quot.sound`;
- documented bridge specifications: `string_eq_spec`, `string_clone_spec`;
- documented extracted opaque operations:
  `Str.Insts.AllocBorrowToOwnedString.to_owned`,
  `alloc.string.String.Insts.CoreCloneClone.clone`, and
  `alloc.string.String.Insts.CoreCmpPartialEqString.eq`; and
- `types.AgentId.root._native.decide.ax_1`, the generated/native root-name residual.

The theorem closure contains no `sorryAx`, and the handwritten refinement contains no `sorry`,
`admit`, or undeclared project-local authority beyond the two named String bridge specifications.
Always state the trusted extractor and the `CapacityOK`/`OracleFidelity` hypotheses when citing the
end-to-end result.
