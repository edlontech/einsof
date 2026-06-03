import ArgusLean.Refinement.Actions.RegisterTool
import ArgusLean.Refinement.Actions.SentinelRefreshBudget
import ArgusLean.Refinement.Actions.ReturnUnendorsed
import ArgusLean.Refinement.Actions.InvokeComplete
import ArgusLean.Refinement.Actions.InvokeStart

/-! # Refinement — per-action simulation index

Index for the per-action forward-simulation proofs under `Refinement/Actions/`. Each holds an
inversion lemma (`<action>_ok_inv`) + a simulation theorem (`<action>_refines`) against that action's
*slice* relation `R<action>`, all cloned from the `RegisterTool` exemplar. This file states no
theorem of its own.

The end-to-end "every reachable kernel state refines the spec" result is assembled separately,
against the single *unified* relation `R`, in `Refinement/Unified/` (`Unified/Bundle.lean`'s
`step_refines`, composed to `implementation_sound` in `Unified/Soundness.lean`).

Originally the per-action layer fanned out to all 12 transitions (the C2 milestone). Once the unified
`R` assembly (Layer 1 + 2) landed, the slice proofs the Unified layer never consumes were pruned
(2026-06-03) — git history preserves them. What remains is the exemplar plus the slice proofs whose
lemmas the oracle/loop-heavy `Unified/Preservation/*` files actually reuse:

* [x] `register_tool`        — Actions/RegisterTool.lean (exemplar / template; see
                               `docs/register_tool_walkthrough.md`)
* [x] `sentinel_refresh_budget` — Actions/SentinelRefreshBudget.lean (capability-gated budget reset;
                               `Preservation/SentinelRefreshBudget` reuses its `_ok_inv`)
* [x] `invoke_start`        — Actions/InvokeStart.lean. The heaviest action: the three-check invoke
                               gate (capability CHECK 1 + graduated flow gate in three sweeps 2a/2b/2c
                               + authorizer CHECK 3) plus speculative taint. Refines against `Rstart`;
                               `Preservation/InvokeStart` reuses `invoke_start_refines`.
* [x] `invoke_complete`     — Actions/InvokeComplete.lean. Loop-free; branches on the single
                               `zero_taint` conformance gate. Hosts the reusable remove-from collection
                               specs + `invocationId_ne_spec` + `completeEndorsed` that
                               `Preservation/InvokeComplete` / `NodupPreservation` consume.
* [x] `return_unendorsed`   — Actions/ReturnUnendorsed.lean. The double-loop egress-gated action;
                               `Preservation/ReturnUnendorsed` reuses `return_unendorsed_refines`.
* [x] `sentinel_elevate_taint` — Actions/SentinelElevateTaint.lean (imported transitively). The
                               single-loop egress-gated keystone; `Preservation/SentinelElevateTaint`
                               reuses `sentinel_elevate_taint_refines`.
-/
