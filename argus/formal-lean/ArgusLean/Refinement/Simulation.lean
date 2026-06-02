import ArgusLean.Refinement.Actions.RegisterTool
import ArgusLean.Refinement.Actions.LoadInstruction
import ArgusLean.Refinement.Actions.Delegate
import ArgusLean.Refinement.Actions.CascadeRevoke
import ArgusLean.Refinement.Actions.Revoke

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
* [ ] `grant_capability`
* [x] `revoke`               — Actions/Revoke.lean (10/10 fields against `Rcasc`; the direct-removal
                               sibling of `cascade_revoke` — same proof modulo the parent-active gate
                               polarity and removing `target`; reuses all cascade bridging, no new axioms)
* [x] `cascade_revoke`       — Actions/CascadeRevoke.lean (10/10 fields against `Rcasc`, the
                               active-guarded-budget variant of `Rdel`; new bridging: `VecMap.get`
                               last-match read, `VecSet.remove`, `agent_parent_drop_child` key-filter,
                               `vmLastEntry_filter_removeKept`; +1 axiom `optionAgentId_ne_spec`)
* [ ] `invoke_start`
* [ ] `invoke_complete`
* [ ] `return_endorsed`
* [ ] `return_unendorsed`
* [ ] `sentinel_elevate_taint`
* [ ] `sentinel_refresh_budget`
-/
