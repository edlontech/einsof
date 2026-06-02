import ArgusLean.Refinement.Actions.RegisterTool
import ArgusLean.Refinement.Actions.LoadInstruction
import ArgusLean.Refinement.Actions.Delegate
import ArgusLean.Refinement.Actions.CascadeRevoke
import ArgusLean.Refinement.Actions.Revoke
import ArgusLean.Refinement.Actions.GrantCapability
import ArgusLean.Refinement.Actions.SentinelRefreshBudget
import ArgusLean.Refinement.Actions.ReturnEndorsed

/-! # Refinement — simulation bundle

Aggregator for the per-action forward-simulation proofs. Each of the 12 TzimtzumV2
transitions gets its own file under `Refinement/Actions/`, holding an inversion lemma
(`<action>_ok_inv`) + a simulation theorem (`<action>_refines`) + its own axiom audit, all
cloned from the `RegisterTool` exemplar. This file imports them and is where the combined
"all 12 transitions refine" theorem is assembled once the fan-out is complete.

C2 fan-out checklist (mirrors the spec's `Tzimtzum/Check*.lean` files):

* [x] `register_tool`        — Actions/RegisterTool.lean (exemplar / template)
* [x] `load_instruction`     — Actions/LoadInstruction.lean (nested `agent_instruction` write)
* [x] `delegate`             — Actions/Delegate.lean (10/10 fields; `agent_parent` closed via the
                               `vmNodupKeys` key-uniqueness invariant carried by `Rdel` +
                               `agent_parent_drop_endpoint` rebuild spec; plus the
                               `VecMap.remove`/`insert` get-machinery + `clear_agent_state` spec)
* [x] `grant_capability`     — Actions/GrantCapability.lean (single nested `agent_cap` write against
                               `Rgrant` (nested `vmsMem` view); reuses `insert_into`, new
                               `set_contains` forward + `get_cloned` bridging + proved `CapKind`
                               eq/clone; no root ⇒ no `sorryAx`/`AgentId.root` residual)
* [x] `revoke`               — Actions/Revoke.lean (10/10 fields against `Rcasc`; the direct-removal
                               sibling of `cascade_revoke` — same proof modulo the parent-active gate
                               polarity and removing `target`; reuses all cascade bridging, no new axioms)
* [x] `cascade_revoke`       — Actions/CascadeRevoke.lean (10/10 fields against `Rcasc`, the
                               active-guarded-budget variant of `Rdel`; new bridging: `VecMap.get`
                               last-match read, `VecSet.remove`, `agent_parent_drop_child` key-filter,
                               `vmLastEntry_filter_removeKept`; +1 axiom `optionAgentId_ne_spec`)
* [x] `sentinel_refresh_budget` — Actions/SentinelRefreshBudget.lean (capability-gated budget reset;
                               two read gates then `VecMap.remove` on `agent_budget`. Refines against
                               `Rrefresh`, the *unguarded* `Rdel`-style budget clause: `agent` stays
                               active, so delete-then-read-as-`bl5` is the observable, faithful image.
                               Reuses `set_contains` + `vecMapRemove_spec`; no new axioms, no root)
* [x] `return_endorsed`      — Actions/ReturnEndorsed.lean (capability-gated, recipient-budget-charged
                               declassification; budget-only write. Refines against `Rret`, whose
                               budget clause is the get-style `budgetReadC` convention — the read the
                               kernel's `budget`/`debit_budget` literally compute — tied to the
                               abstract lattice through the injective `budgetC`. New shared bridging:
                               `budget_spec` / `budgetExhausted_spec` / `debitBudget_spec` (budget
                               reads/writes), `vecMapKVecSetSetNonempty_spec` + `vmsMemLast` +
                               `vecSetIsEmpty_spec` (the `set_nonempty` in-flight gate), proved
                               `BudgetLevel` eq/clone/debit (`debitC`). No new axioms beyond
                               `optionAgentId_ne_spec`; no root ⇒ no `sorryAx`/`AgentId.root`)
* [ ] `invoke_start`
* [ ] `invoke_complete`
* [~] `return_unendorsed`   — FOUNDATION DONE, assembly TODO. Reusable building blocks proven +
                               committed: in `Collections.lean` the leaf specs `vecSetUnionWith_spec`,
                               `extendInto_spec` (last-match `vmsMemLast` write), `getSetOrEmpty_spec`,
                               `vecMapKVecSetSetNonempty_spec` + `vecSetIsEmpty_spec`, plus
                               `OverrideEntry`/`ConfLevel`/`BudgetLevel` eq/clone; in
                               `ReturnUnendorsedFlow.lean` the oracle reads `flowMode_spec` (+`flowModeC`),
                               `hasFlowOverride_spec`, `overrideConsumed_spec` (+`FlowKey`/`EgressKind`/
                               `OverrideKey`/`FlowMode` eq/clone). REMAINING: the inner loop
                               (`return_unendorsed_loop0_loop0`, per-level fold over `parent_flights`
                               calling `gate_egress`) + outer loop (over `child_taint` levels) specs,
                               an oracle-agreement relation `Rretu` (content-gate totality is the only
                               opaque oracle to assume), and the inversion+refines assembly relating
                               the loop accumulator's `denied`/`to_consume` to the abstract flow-gate
                               guard + `override_used` write. The refinement direction is sound:
                               kernel success (denied=false) is strictly stronger than the abstract
                               guard (kernel ignores override at Inspect mode; abstract allows it), and
                               `to_consume` matches the abstract `override_used` add-condition *under
                               the guard*.
* [~] `sentinel_elevate_taint` — KEYSTONE LOOP SPEC DONE, refines assembly TODO. The in-flight loop
                               (`sentinelLoop_spec`, Actions/SentinelElevateTaint.lean) is PROVEN +
                               verified in the build: it folds `gate_egress` over `agent`'s in-flight
                               invocations (per-tool oracle values `cgOf`/`ovOf`/`ocOf`, the
                               `missing_binding` flag, Nodup+capacity tracking), characterising the
                               final `denied`/`to_consume`/`missing_binding` via `invDenied` /
                               `invConsumed` / `invMissing`. Built on `gateEgress_spec` + the leaf/
                               oracle foundation (`get_set_or_empty`, `extend_into`, `flow_mode`,
                               `has_flow_override`, `override_consumed`, `tool_metadata`, `ovC`/`ocC`,
                               `confA`). This is the same inner-loop machinery `return_unendorsed`
                               reuses (its double loop = this loop nested under a `child_taint` loop).
                               REMAINING: the `Rsent` oracle-agreement relation + the inversion/refines
                               assembly — peel the active gate, apply `sentinelLoop_spec`, discharge
                               the `missing_binding`/`denied` gates, and match the three writes
                               (`extend_into override_used`, `insert_into taint_levels`/
                               `gh_taint_invoked`) to the abstract updates. The soundness is verified by
                               hand, incl. the subtle **single-use `override_used`** correspondence:
                               `to_consume` ↔ the abstract `override_used` add holds *under the gate*
                               via "∃ Deny-egress ⇒ override present ∧ not-yet-consumed" (the guard
                               forces `ov∧¬oc` at every `Deny` egress).
-/
