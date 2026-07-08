# argus-kernel Lean refinement (`formal-lean`)

Mechanically-extracted Lean model of the Rust `argus-kernel`, refined against the
pure-Lean TzimtzumV3 (Kav) spec. The end-to-end result is `implementation_sound`: every
reachable state of the extracted kernel refines an abstract TzimtzumV3 state that
satisfies all safety invariants (11 safeties + 15 strengthening invariants, 16 actions).

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
      FlowBridging.lean             flow_decision / gate_egress / integ_decision / egressDenied
      FlowOracle.lean               flow-oracle reads (flowModeC/toolMetaC/...) + per-invocation
                                    helpers (invToolC/egItems/...); general flow bridging
    PlausibleChecks.lean            opt-in property-test harness; `lake build ArgusChecks`
    Unified/
      ViewCoincidence.lean          the canonical-view facts the unified relation needs
      NodupPreservation.lean        key-uniqueness preservation across writes
      Relation.lean                 the unified relation `R` + per-invocation oracle-agreement
                                    (CgAgree/AuAgree/CfAgree/RcAgree)
      Bridges.lean                  shared `R`-projection helpers for the preservation proofs
      Preservation/<Action>.lean    per-transition `<action>_preservesR` (15 files; InvokeComplete
                                    proves the split pair, the event's `endorsed` selecting the
                                    spec action)
      InitRefinement.lean           the initial state refines the abstract initial state
      Bundle.lean                   `KernelCmd` dispatch + `step_refines`: 15 transitions
                                    refining the 16 spec actions in one statement
      Soundness.lean                `implementation_sound` (init refinement, forward simulation, Kav)
```

Layering is strict: `Generated` then `Bridging` then `Unified`. Nothing in `Bridging` or
`Generated` depends on `Unified`.

## What `implementation_sound` proves, and what it doesn't

For every reachable concrete `KernelState c`, there is an abstract state `a` with
`R c bg a` and `Tzimtzum.allInv a` (every TzimtzumV3 safety invariant holds — including
`integrity_confinement`, the prompt-injection containment headline). It is forward
simulation composed with the Kav soundness theorem.

It is sound modulo the trusted extractor and two explicit assumptions. It does not prove
the hand-written Rust source, the oracles, or the SPIFFE/STS mesh and Elixir adapter
correct. State the extractor and the assumptions whenever claiming end-to-end soundness.

## Trust base (TCB)

`#print axioms ArgusLean.Refinement.implementation_sound` reports exactly:

- Standard: `propext`, `Classical.choice`, `Quot.sound`.
- `sorryAx`, inherited from the Aeneas standard library (`Aeneas/Std/Slice.lean` and the
  String iterator files carry documented `sorry`s) — an extractor-library residual, not a
  `sorry` in this refinement's own proofs.
- Named-root: `argus_kernel.types.AgentId.root._native.decide.ax_1`, the `native_decide`
  residual for the root agent's concrete name. This is a baseline of naming the root, not
  a proof `sorry`.
- Opaque id/String ops (7, in `Bridging/Collections.lean`): `string_eq_spec`,
  `string_clone_spec`, `agentId_ne_spec`, `optionAgentId_ne_spec`, `invocationId_ne_spec`,
  `overrideKey_ne_spec`, `toolId_ne_spec`, stating that the extracted opaque
  `String`-backed decidable (dis)equality and clone behave faithfully.
- Aeneas/Charon extractor residuals (in `Generated/ArgusKernel.lean`): the per-type
  `...CmpPartialEq....ne` / `...eq` / `...clone` / `to_owned` instance axioms the extractor
  emits for the opaque `String`-backed identifier types.

Two assumptions are hypotheses of `implementation_sound` (discharged by the caller, not
axioms):

- `CapacityOK`: the `Vec`-capacity bounds (`... .length < Usize.max`) each transition
  needs, plus `invoke_start`'s two per-invocation oracle-seam predictions (the abstract
  tool binding and the fresh invocation's attested-egress agreement). There is no
  resource model here to discharge the bounds; the predictions are the per-call half of
  the oracle contract.
- `OracleFidelity`: the runtime `ContentGate` / `Authorizer` / `Conformance` oracles agree
  with a fixed per-invocation abstract interpretation (`cgRel`/`auRel`/`cfRel` keyed by
  `InvocationId`; `return_conforms` pairwise).

There are no proof `sorry`s in this refinement's own files; the verification is
kernel-checked.
