import ArgusLean.Refinement.Actions.RegisterTool
import ArgusLean.Refinement.Actions.LoadInstruction
import ArgusLean.Refinement.Actions.Delegate
import ArgusLean.Refinement.Actions.CascadeRevoke
import ArgusLean.Refinement.Actions.Revoke
import ArgusLean.Refinement.Actions.GrantCapability
import ArgusLean.Refinement.Actions.SentinelRefreshBudget
import ArgusLean.Refinement.Actions.ReturnEndorsed
import ArgusLean.Refinement.Actions.ReturnUnendorsed
import ArgusLean.Refinement.Actions.InvokeComplete
import ArgusLean.Refinement.Actions.InvokeStart

/-! # Refinement — per-action simulation index

Import aggregator for the 12 per-action forward-simulation proofs. Each TzimtzumV2 transition gets
its own file under `Refinement/Actions/`, holding an inversion lemma (`<action>_ok_inv`) + a
simulation theorem (`<action>_refines`) against that action's *slice* relation `R<action>` + its own
axiom audit, all cloned from the `RegisterTool` exemplar.

This file states no theorem of its own — it is the index for the per-action layer. The end-to-end
"every reachable kernel state refines the spec" result is assembled separately, against the single
*unified* relation `R`, in `Refinement/Unified/` (`Unified/Bundle.lean`'s `step_refines`, composed to
`implementation_sound` in `Unified/Soundness.lean`). The per-action `_refines`/`_ok_inv` lemmas below
feed that assembly for the oracle/loop-heavy actions — see each `Unified/Preservation/*` file.

C2 fan-out (mirrors the spec's `Tzimtzum/Check*.lean` files):

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
* [x] `invoke_start`        — Actions/InvokeStart.lean. The heaviest action: the
                               three-check invoke gate (capability CHECK 1 + graduated flow gate in three
                               sweeps 2a/2b/2c + authorizer CHECK 3) plus speculative taint. Refines
                               against `Rstart` (last-match `vmsMemLast` views of `agent_cap`/`in_flight`/
                               `taint_levels`/`override_used`, one-directional `invocation_tool`, immutable
                               flow oracles as in `Rsent`, the named root pinned by `AgentId.root =
                               .ok a.root_agent`, metadata `tool_conf_floor`/`tool_cap` correspondences,
                               and the well-formedness invariant "every in-flight invocation is bound to a
                               tool *with metadata*" — needed for the 2a speculative-taint bridge). New
                               gate specs `containsKey_spec` (b3, inv unbound) + `anyValueContains_spec`
                               (b4, inv not in flight) + the last-match `vecMapKVecSetInsertInto_vmLast_spec`
                               for the `in_flight` write (the find loop picks the last key-match, so no
                               key-uniqueness needed). `invoke_start_ok_inv` peels the 5 gates + reads `m`,
                               runs the capability fold + the three flow sweeps (`invoke_start_loop1` over
                               `speculative_taint`, `invoke_start_loop2` over in-flight tools,
                               `gate_egress` for the new tool), and reads off the three writes
                               (`extend_into override_used`, `VecMap.insert invocation_tool`,
                               `insert_into in_flight`). `invoke_start_refines` establishes the three
                               abstract flow guards from `denied = false` via `not_egressDenied_disj`,
                               and the three-clause single-use `override_used` correspondence via per-sweep
                               `egressConsumed_iff_abstractDenied`. `content_gate_passes`/`authorizer_allows`
                               are the two opaque oracles (`hcg`/`hcgA`, `hau`/`hauA`); `a.invocation_tool
                               inv = tool` is the abstract's prediction of the new binding (`hinvtool`).
                               Gotcha: `subst` on `ag = agent` wrongly eliminates `agent` (pass the eq
                               explicitly). Axiom-clean: standard three + `String`/id residuals.
* [x] `invoke_complete`     — Actions/InvokeComplete.lean. Loop-free; branches on the single
                               `zero_taint` conformance gate. Refines against `Rcomplete` (last-match
                               `vmsMemLast` `in_flight`, insert-view `vmsMem` taint/gh, get-style
                               `budgetReadC` budget, metadata `tool_conf_floor`/`tool_output_bounded`
                               correspondences, + the well-formedness invariant ruling out the kernel's
                               defensive no-binding/no-metadata exits). `invoke_complete_ok_inv` peels the
                               `set_contains` + active gates, the `remove_from` point-clear, and reads the
                               metadata; the nested `if output_bounded/conforms/¬exhausted` reduces to
                               `completeEndorsed` and the kernel branches endorsed (`debitBudget_spec`) vs
                               unendorsed (two `insert_into` of `conf_floor`). `invoke_complete_refines`
                               matches the abstract endorsed condition via the metadata correspondences +
                               `hcfA`; the budget debit reuses the `return_endorsed` lattice technique.
                               `output_conforms` is the one opaque oracle (state-independent `hcf`/`hcfA`).
                               Gotcha: the do-notation tuple-`let (conf_floor, output_bounded)` needs full
                               `simp at hok` (collapses it + reduces `decide ¬b3 → !bexh`); `subst` on
                               `G = agent` wrongly eliminates `agent` (use `rw`). Axiom-clean: standard
                               three + `String`/id residuals + `invocationId_ne_spec`.
* [x] `return_unendorsed`   — Actions/ReturnUnendorsed.lean. Refines against `Rretu` (the
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
* [x] `sentinel_elevate_taint` — Actions/SentinelElevateTaint.lean. Refines against `Rsent`
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
