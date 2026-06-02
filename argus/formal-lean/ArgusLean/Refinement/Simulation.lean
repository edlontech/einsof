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
* [ ] `return_unendorsed`
* [ ] `sentinel_elevate_taint` — the flow-gate bridging foundation it needs (and `invoke_start` /
                               `return_*` reuse) is DONE in `Refinement/FlowBridging.lean`:
                               `flowDecision_spec` (3-way decision) + `gateEgress_spec` (egress fold)
                               + `vecSetInsertNodup_spec` / `overrideKey_eq_spec`. Remaining for the
                               action: an oracle-agreement relation, `Relev` (get-style
                               `override_used`), the outer in-flight loop, `get_set_or_empty` /
                               `extend_into` specs.
-/
