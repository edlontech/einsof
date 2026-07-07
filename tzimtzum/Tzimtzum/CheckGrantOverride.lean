import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def grantOverride : KAgent → KAgent → KTool → ConfLevel → Kav.Action KSt :=
  grant_override

-- Group A: invariants frame-trivial w.r.t. the three modified relations
-- (`flow_override` / `override_used` / `agent_budget`), except `revocation_clean` (manual
-- proof below: the cascade stalls on the classical `ite` inside the untouched
-- `agent_budget` conjunct, unrelated to `revocation_clean`'s own logic).
private def invsA : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ∈
    (["root_always_active", "default_deny", "capability_subsumption",
      "tool_attestation_intact", "instruction_attestation_intact",
      "parent_implies_active", "single_parent", "no_self_parent", "root_no_parent",
      "in_flight_active", "in_flight_registered", "in_flight_unique", "root_all_caps",
      "root_no_in_flight"] : List String))

#kav_check_action grantOverride invsA

-- Group B: the flow/override/budget-sensitive invariants. The re-arm guard
-- (`∀ I, ¬ s.in_flight target I`) makes the single-use invariants vacuous for the target;
-- for A ≠ target nothing in the three modified relations changes.
private def invsB : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ∈
    (["flow_confinement", "flow_confinement_weak",
      "override_consumed_when_sole_justification", "budget_bounded",
      "in_flight_flow_compat", "in_flight_override_consumed",
      "in_flight_egress_attested", "in_flight_implies_used"] : List String))

#kav_check_action grantOverride invsB

-- Manual proof of the one resistant VC: `revocation_clean` under `grant_override`.
theorem grant_override_pres_revocation_clean
    (granter target : KAgent) (tool : KTool) (lvl : ConfLevel) (s s' : KSt)
    (hrc : revocation_clean s)
    (_hg : (grantOverride granter target tool lvl).guard s)
    (hn : (grantOverride granter target tool lvl).next s s') :
    revocation_clean s' := by
  unfold revocation_clean grantOverride grant_override Kav.Action.next at *
  have hactive : s'.agent_active = s.agent_active := by grind
  intro A I L hna
  rw [hactive] at hna
  obtain ⟨hinf, htaint⟩ := hrc A I L hna
  exact ⟨by grind, by grind⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms grant_override_pres_revocation_clean

end Tzimtzum
