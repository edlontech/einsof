import ArgusLean.Refinement.Actions.RegisterTool
import ArgusLean.Refinement.Actions.LoadInstruction
import ArgusLean.Refinement.Actions.Delegate
import ArgusLean.Refinement.Actions.CascadeRevoke
import ArgusLean.Refinement.Actions.Revoke
import ArgusLean.Refinement.Actions.GrantCapability
import ArgusLean.Refinement.Actions.SentinelRefreshBudget
import ArgusLean.Refinement.Actions.ReturnEndorsed
import ArgusLean.Refinement.Actions.ReturnUnendorsed

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
* [x] `return_unendorsed`   — DONE 10/12 (Actions/ReturnUnendorsed.lean). Refines against `Rretu` (the
                               last-match `vmsMemLast` oracle-agreement relation: `in_flight` via the
                               `set_nonempty`/`get_set_or_empty` reads, `taint_levels`/`gh_taint_received`
                               via the `get_set_or_empty` read + `extend_into` write, `override_used` via
                               `override_consumed`/`extend_into`; `agent_parent` get-style; immutable flow
                               oracles as in `Rsent`; plus the **well-formedness** binding-totality
                               conjunct the abstract guard needs). The DOUBLE loop accumulates the per-
                               `(level, inv)` flow decision: `returnUnendInner_spec` (per-level fold over
                               `parent_flights`, the `sentinelLoop_spec` machinery minus `missing_binding`,
                               reusing `invDenied`/`invConsumed`) nested under `returnUnendOuter_spec`
                               (fold over `child_taint` levels, multiplicative `|ct|*|pf|` capacity).
                               `return_unendorsed_ok_inv` peels the 4 gates, runs the double loop, and
                               reads off the three `extend_into` writes uniformly across the two `is_empty`
                               branches (full `simp` collapses the tuple-bind pattern-`let (vm, vm1)`).
                               `return_unendorsed_refines` establishes the abstract flow guard from
                               `denied = false` via `not_egressDenied_disj`, and the single-use
                               `override_used` correspondence via `egressConsumed_iff_abstractDenied`. The
                               content gate is the one opaque oracle (`hcg`/`hcgA`). Axiom-clean: standard
                               three + `String`/id residuals + `optionAgentId_ne_spec`.
* [x] `sentinel_elevate_taint` — DONE 9/12 (Actions/SentinelElevateTaint.lean). Refines against `Rsent`
                               (the oracle-agreement relation: `agent_active`/`taint_levels`/
                               `gh_taint_invoked` via the insert `vmsMem` view, `in_flight`/
                               `override_used` via the last-match `vmsMemLast` view that `get_set_or_empty`
                               / `override_consumed` / `extend_into` observe, plus the immutable flow
                               oracles `tool_egress`→`egItems`, `flow_allows`/`flow_inspects`→`flowModeC`
                               branches, `flow_override`→override-entry membership, `invocation_tool`
                               one-directional). `sentinel_elevate_taint_ok_inv` peels the active gate,
                               applies `sentinelLoop_spec`, discharges the `missing_binding`/`denied`
                               gates (full `simp` reduces the tuple-bind pattern-`let`), and reads off the
                               three writes (`extend_into override_used`, `insert_into taint_levels`/
                               `gh_taint_invoked`). `sentinel_elevate_taint_refines` establishes the
                               abstract flow guard from the concrete `denied = false` via the pure
                               `not_egressDenied_disj`, and the single-use `override_used` correspondence
                               via `egressConsumed_iff_abstractDenied` — the keystone collapse: under the
                               guard, "∃ Deny-egress ⇒ override present ∧ not-yet-consumed", so the
                               abstract "denied-modulo-override" add coincides with the concrete
                               `to_consume`. Content gate is the one opaque oracle (`hcg` totality + `hcgA`
                               agreement, supplied separately). Axiom-clean: no `sorryAx`, only the
                               standard `String`/decidable-eq extractor residuals. The same inner-loop
                               machinery `return_unendorsed` reuses (its double loop = this loop nested
                               under a `child_taint` loop).
-/
