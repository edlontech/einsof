import Tzimtzum.Actions
import Tzimtzum.Soundness.Bundle
import Tzimtzum.OpaqueTypes
import Kav.Reachable
import Kav.Engine
import Lean

/-!
# Shared soundness infrastructure

The macros split invariant conjunctions and run each resulting goal with a fresh heartbeat budget.
The full cascade unfolds admission gates; the lite cascade keeps them opaque for frame-preservation
obligations. `ksystem` instantiates the protocol transition system at the opaque verification sorts.
-/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

open Lean Lean.Elab.Tactic in
/-- Run `tac` on every current goal, each under a fresh heartbeat budget. -/
elab "all_goals_fresh " tac:tacticSeq : tactic => do
  let goals ← getGoals
  let mut acc : Array MVarId := #[]
  for g in goals do
    unless (← g.isAssigned) do
      setGoals [g]
      Core.withCurrHeartbeats (evalTactic tac)
      acc := acc ++ (← getGoals).toArray
  setGoals acc.toList

/-- The names every cascade unfolds: the bundle, the conjuncts, the derived gates, and the
`Kav.Action` projections. -/
macro "tzimtzum_simp_core" head:ident : tactic => `(tactic| (
  try simp only [$head:ident, allInv_iff, invS_iff, invP_iff, invPP_iff, invE_iff, invC_iff,
    root_always_active, parent_implies_active, single_parent, no_self_parent,
    root_no_parent, capability_subsumption, root_all_caps, revocation_clean, pending_active,
    pending_unique, pending_registered, root_no_pending, pending_ids_consumed,
    pending_egress_attested, pending_snapshot_coherent, default_deny,
    flow_confinement, flow_confinement_weak,
    integrity_confinement, integrity_confinement_weak, clearance_confinement,
    pending_flow_compat, pending_integ_compat,
    challenge_scoped, challenges_enforce_only, challenge_unique,
    inspected_evidence_consumed, bypass_mode_sound, quarantine_pending,
    grant_bounded, grant_active, grant_pinned,
    St.flow_allows, St.flow_inspects, integ_allows, integ_inspects, clearance_admits,
    contained, vouched,
    Tzimtzum.speculative_taint, Tzimtzum.speculative_taint_contained,
    Tzimtzum.speculative_integ,
    Kav.Action.guard, Kav.Action.next] at *))

/-- Full cascade: gate predicates unfolded. For the conjuncts the gate makes inductive. -/
macro "kav_discharge " head:ident : tactic => `(tactic| (
  (try simp only [allInv_iff, invS_iff, invP_iff, invPP_iff, invE_iff, invC_iff]);
  (repeat' apply And.intro);
  all_goals_fresh (
    (tzimtzum_simp_core $head) <;>
    (try simp only [beginAllow, beginAdmissible, checkCapability, checkClearance,
        checkFlowStrict, checkFlowAdmissible, checkIntegStrict, checkIntegAdmissible,
        authorizeAdmits, endorsedOK, crossHolds,
        ingestHolds, ingestConfHold, ingestClearHold, ingestIntegHold] at *) <;>
      (first | trivial | grind | (simp_all <;> grind) | auto | duper [*]))))

/-- Lite cascade: gate predicates as atoms. For frame-ish conjuncts. -/
macro "kav_discharge_lite " head:ident : tactic => `(tactic| (
  (try simp only [allInv_iff, invS_iff, invP_iff, invPP_iff, invE_iff, invC_iff]);
  (repeat' apply And.intro);
  all_goals_fresh (
    (tzimtzum_simp_core $head) <;>
      (first | trivial | grind | (simp_all <;> grind) | auto | duper [*]))))

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- `Preserves act P`: from any state satisfying the full bundle whose guard admits `act`,
every `next`-successor satisfies `P`. Per-action check files state one `Preserves` theorem
per sub-bundle and compose them into the `allInv` result consumed by `Soundness.lean`. -/
def Preserves
    (act : Kav.Action (St AgentId ToolId InvocationId CapKind EgressKind ChallengeId
      AttestationId CrossingId AssignmentDigest PolicyDigest ContentHash))
    (P : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash → Prop) : Prop :=
  ∀ s s', allInv s → act.guard s → act.next s s' → P s'

/-- The TzimtzumV4 transition system at the opaque audit sorts. -/
def ksystem : Kav.TransitionSystem KSt := system

end Tzimtzum
