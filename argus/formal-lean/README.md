# argus-kernel Lean refinement (`formal-lean`)

Mechanically-extracted Lean model of the Rust `argus-kernel`, refined against the
pure-Lean TzimtzumV2 (Kav) spec. The end-to-end result is `implementation_sound`: every
reachable state of the extracted kernel refines an abstract TzimtzumV2 state that
satisfies all safety invariants.

The Rust kernel is extracted to Lean with Charon and Aeneas
(`scripts/charon-aeneas-extract.sh` produces `ArgusLean/Generated/ArgusKernel.lean`); this
library proves the extracted model refines the spec.

## Build

```bash
lake build              # the whole library, incl. implementation_sound
lake build ArgusChecks  # opt-in Plausible property-test harness (not in the default build)
```

Lean 4.30 (pinned via `lean-toolchain`). After a toolchain change, run `lake exe cache get`
first.

## Module map

```
ArgusLean.lean                      root: Generated + Smoke + Unified.{Bundle,Soundness}
ArgusLean/
  Generated/ArgusKernel.lean        Aeneas/Charon-extracted kernel model; DO NOT EDIT
  Refinement/
    Bridging/                       reusable spec-bridging: concrete Result/loop to list-level facts
      Collections.lean              VecMap/VecSet last-match insert/remove specs; id/String trust axioms
      StateRelation.lean            AbsState, confC/budgetC, capMem/budgetReadC, clear/budget specs
      FlowBridging.lean             flow_decision / gate_egress / egressDenied / egressConsumed
      FlowOracle.lean               flow-oracle reads (flowModeC/toolMetaC/...) + per-invocation
                                    flow contribution (invToolC/invDenied/...); general flow bridging
    PlausibleChecks.lean            opt-in property-test harness; `lake build ArgusChecks`
    Unified/
      ViewCoincidence.lean          the canonical-view facts the unified relation needs
      NodupPreservation.lean        key-uniqueness preservation across writes
      Relation.lean                 the unified relation `R` + oracle-agreement (CgAgree/AuAgree/CfAgree)
      Bridges.lean                  shared `R`-projection helpers for the preservation proofs
      Preservation/<Action>.lean    per-action `<action>_preservesR`. The oracle/loop-heavy actions
                                    (invoke_start, return_unendorsed, sentinel_elevate_taint) also carry
                                    their slice relation + `_refines` here; the rest prove `R` directly.
      InitRefinement.lean           the initial state refines the abstract initial state
      Bundle.lean                   `step_refines`: the 13 actions collapsed into one statement
      Soundness.lean                `implementation_sound` (init refinement, forward simulation, Kav)
```

Layering is strict: `Generated` then `Bridging` then `Unified`. Nothing in `Bridging` or
`Generated` depends on `Unified`.

## What `implementation_sound` proves, and what it doesn't

For every reachable concrete `KernelState c`, there is an abstract state `a` with
`R c bg a` and `Tzimtzum.allInv a` (every TzimtzumV2 safety invariant holds). It is forward
simulation composed with the Kav soundness theorem.

It is sound modulo the trusted extractor and two explicit assumptions. It does not prove
the hand-written Rust source, the oracles, or the SPIFFE/STS mesh and Elixir adapter
correct. State the extractor and the assumptions whenever claiming end-to-end soundness.

## Trust base (TCB)

`#print axioms ArgusLean.Refinement.implementation_sound` reports exactly:

- Standard: `propext`, `Classical.choice`, `Quot.sound`.
- Named-root: `argus_kernel.types.AgentId.root._native.decide.ax_1`, the `native_decide`
  residual for the root agent's concrete name. This is a baseline of naming the root, not
  a proof `sorry`.
- Opaque id/String ops (6, in `Bridging/Collections.lean`): `string_eq_spec`,
  `string_clone_spec`, `agentId_ne_spec`, `optionAgentId_ne_spec`, `invocationId_ne_spec`,
  `overrideKey_ne_spec`, stating that the extracted opaque `String`-backed decidable
  (dis)equality and clone behave faithfully.
- Aeneas/Charon extractor residuals (in `Generated/ArgusKernel.lean`): the per-type
  `...CmpPartialEq....ne` / `...eq` / `...clone` / `to_owned` instance axioms the extractor
  emits for the opaque `String`-backed identifier types.

Two assumptions are hypotheses of `implementation_sound` (discharged by the caller, not
axioms):

- `CapacityOK`: the `Vec`-capacity bounds (`... .length < Usize.max`) each transition
  needs. There is no resource model here to discharge them.
- `OracleFidelity`: the runtime `ContentGate` / `Authorizer` / `Conformance` oracles agree
  with the abstract state's oracle fields.

There are no proof `sorry`s in the refinement; the verification is kernel-checked.
