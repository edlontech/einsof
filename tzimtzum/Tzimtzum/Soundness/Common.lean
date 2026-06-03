import Tzimtzum.OpaqueTypes
import Kav.Reachable
import Kav.Engine
import Lean

/-! # C0 soundness bundle — shared infrastructure

Split out of the former monolithic `Tzimtzum/Soundness.lean` so `lake` caches and
parallelises each action's preservation proof independently (the two budget actions
`invoke_complete` / `return_endorsed` dominated the build, so they live in their own
modules and no longer force the other ten to recompile).

This module holds the pieces every preservation module shares:

* `allInv` — the 25-conjunct invariant bundle (10 safeties + 15 strengthening), in
  `allInvariants` order.
* `all_goals_fresh` — run a tactic on each goal under a FRESH heartbeat budget
  (`Core.withCurrHeartbeats`), mirroring the per-VC freshness that makes
  `#kav_check_action` succeed where one shared budget starves.
* `kav_discharge` — split the bundle goal into its 25 conjuncts and discharge each
  under that fresh budget with the kernel-checked cascade.
* `ksystem` — the TzimtzumV2 system monomorphised at the opaque `KSt` sorts. -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

/-- The full TzimtzumV2 invariant bundle, in the order of `allInvariants`.

    Sort-polymorphic: monomorphising at the opaque `KSt` (the `#kav_check` audit sorts) is just one
    instance. The concrete-sort refinement (`argus/formal-lean`) instantiates it at the extracted
    `String`-backed id types via the polymorphic soundness bundle (`kav_soundP`). -/
def allInv (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  root_always_active s ∧ default_deny s ∧ flow_confinement s ∧ flow_confinement_weak s
  ∧ capability_subsumption s ∧ revocation_clean s ∧ taint_integrity s
  ∧ tool_attestation_intact s ∧ instruction_attestation_intact s
  ∧ override_consumed_when_sole_justification s
  ∧ parent_implies_active s ∧ single_parent s ∧ no_self_parent s ∧ root_no_parent s
  ∧ in_flight_active s ∧ in_flight_registered s ∧ in_flight_unique s ∧ root_all_caps s
  ∧ root_no_in_flight s ∧ budget_unique s ∧ active_has_budget s ∧ ghost_invoked_sound s
  ∧ ghost_received_sound s ∧ in_flight_flow_compat s ∧ in_flight_override_consumed s

open Lean Lean.Elab.Tactic in
/-- Run `tac` on every current goal, each under a FRESH heartbeat budget
    (`Core.withCurrHeartbeats` resets the counter per goal). -/
elab "all_goals_fresh " tac:tacticSeq : tactic => do
  let goals ← getGoals
  let mut acc : Array MVarId := #[]
  for g in goals do
    unless (← g.isAssigned) do
      setGoals [g]
      Core.withCurrHeartbeats (evalTactic tac)
      acc := acc ++ (← getGoals).toArray
  setGoals acc.toList

/-- Split the bundle goal into its 25 atomic conjuncts, then discharge each under a fresh
    heartbeat budget. `$head` is the action `def` (or `initial` for the init VCs); its
    field equations are exposed inside each per-goal window where they cost what one
    `#kav_check_action` VC costs. -/
macro "kav_discharge" head:ident : tactic => `(tactic| (
  (try unfold allInv) <;>
  (try refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩);
  all_goals_fresh (
    (try simp only [$head:ident, allInv,
        root_always_active, default_deny, flow_confinement, flow_confinement_weak,
        capability_subsumption, revocation_clean, taint_integrity, tool_attestation_intact,
        instruction_attestation_intact, override_consumed_when_sole_justification,
        parent_implies_active, single_parent, no_self_parent, root_no_parent,
        in_flight_active, in_flight_registered, in_flight_unique, root_all_caps,
        root_no_in_flight, budget_unique, active_has_budget, ghost_invoked_sound,
        ghost_received_sound, in_flight_flow_compat, in_flight_override_consumed,
        Tzimtzum.speculative_taint, Kav.Action.guard, Kav.Action.next] at *) <;>
      (first | trivial | grind | (simp_all <;> grind) | auto | duper [*]))))

/-- The TzimtzumV2 transition system, monomorphised at the opaque sorts of `KSt`. -/
def ksystem : Kav.TransitionSystem KSt := system

end Tzimtzum
