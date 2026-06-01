import ArgusLean.Refinement.Actions.RegisterTool
import ArgusLean.Refinement.Actions.LoadInstruction

/-! # Refinement — simulation bundle

Aggregator for the per-action forward-simulation proofs. Each of the 12 TzimtzumV2
transitions gets its own file under `Refinement/Actions/`, holding an inversion lemma
(`<action>_ok_inv`) + a simulation theorem (`<action>_refines`) + its own axiom audit, all
cloned from the `RegisterTool` exemplar. This file imports them and is where the combined
"all 12 transitions refine" theorem is assembled once the fan-out is complete.

C2 fan-out checklist (mirrors the spec's `Tzimtzum/Check*.lean` files):

* [x] `register_tool`        — Actions/RegisterTool.lean (exemplar / template)
* [x] `load_instruction`     — Actions/LoadInstruction.lean (nested `agent_instruction` write)
* [ ] `delegate`
* [ ] `grant_capability`
* [ ] `revoke`
* [ ] `cascade_revoke`
* [ ] `invoke_start`
* [ ] `invoke_complete`
* [ ] `return_endorsed`
* [ ] `return_unendorsed`
* [ ] `sentinel_elevate_taint`
* [ ] `sentinel_refresh_budget`
-/
