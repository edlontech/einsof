import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def grantOverride : KAgent → KAgent → KTool → ConfLevel → Kav.Action KSt :=
  grant_override

-- Group A: invariants frame-trivial w.r.t. the three modified relations
-- (`flow_override` / `override_used` / `agent_budget`).
private def invsA : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ∈
    (["root_always_active", "default_deny", "capability_subsumption", "revocation_clean",
      "tool_attestation_intact", "instruction_attestation_intact",
      "parent_implies_active", "single_parent", "no_self_parent", "root_no_parent",
      "in_flight_active", "in_flight_registered", "in_flight_unique", "root_all_caps",
      "root_no_in_flight"] : List String))

#kav_check_action grantOverride invsA

-- Group B: the flow/override/budget-sensitive invariants, except `active_has_budget`
-- (manual proof below, same budget-debit-resistant VC as return_endorsed /
-- invoke_complete). The re-arm guard (`∀ I, ¬ s.in_flight target I`) makes the
-- single-use invariants vacuous for the target; for A ≠ target nothing in the three
-- modified relations changes.
private def invsB : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ∈
    (["flow_confinement", "flow_confinement_weak",
      "override_consumed_when_sole_justification", "budget_unique", "budget_bounded",
      "in_flight_flow_compat", "in_flight_override_consumed"] : List String))

#kav_check_action grantOverride invsB

-- Manual proof of the one resistant VC: `active_has_budget` under `grant_override`.
-- Same shape as `return_endorsed_pres_active_has_budget`: the granter's flat-1 debit post
-- (`∀ b, agent_budget granter b → L = b - 1`) needs a witness the cascade can't reconstruct;
-- we witness `L - 1` and use `budget_unique` to pin every `b` to the `active_has_budget`
-- level `L`.
theorem grant_override_pres_active_has_budget
    (granter target : KAgent) (tool : KTool) (lvl : ConfLevel) (s s' : KSt)
    (hahb : active_has_budget s)
    (hbu : budget_unique s)
    (hg : (grantOverride granter target tool lvl).guard s)
    (hn : (grantOverride granter target tool lvl).next s s') :
    active_has_budget s' := by
  unfold active_has_budget budget_unique grantOverride grant_override Kav.Action.guard
    Kav.Action.next at *
  intro A hactive
  have hactiveS : s.agent_active A := by
    have hfa : s'.agent_active = s.agent_active := by grind
    rw [hfa] at hactive; exact hactive
  have hbeq : ∀ X Y, s'.agent_budget X Y =
      ((X = granter ∧ ∀ b, s.agent_budget granter b → Y = b - 1)
      ∨ (X ≠ granter ∧ s.agent_budget X Y)) := by grind
  by_cases hAg : A = granter
  · subst hAg
    obtain ⟨L, hL⟩ := hahb A hactiveS
    refine ⟨L - 1, ?_⟩
    rw [hbeq]; left
    refine ⟨rfl, ?_⟩
    intro b hb
    have hLb : L = b := hbu A L b ⟨hactiveS, hL, hb⟩
    rw [hLb]
  · obtain ⟨L, hL⟩ := hahb A hactiveS
    exact ⟨L, by rw [hbeq]; right; exact ⟨hAg, hL⟩⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms grant_override_pres_active_has_budget

end Tzimtzum
