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
      "taint_integrity", "tool_attestation_intact", "instruction_attestation_intact",
      "parent_implies_active", "single_parent", "no_self_parent", "root_no_parent",
      "in_flight_active", "in_flight_registered", "in_flight_unique", "root_all_caps",
      "root_no_in_flight", "ghost_invoked_sound", "ghost_received_sound"] : List String))

#kav_check_action grantOverride invsA

-- Group B: the flow/override/budget-sensitive invariants, except `active_has_budget`
-- (manual proof below, same budget-debit-resistant VC as return_endorsed /
-- invoke_complete). The re-arm guard (`∀ I, ¬ s.in_flight target I`) makes the
-- single-use invariants vacuous for the target; for A ≠ target nothing in the three
-- modified relations changes.
private def invsB : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ∈
    (["flow_confinement", "flow_confinement_weak",
      "override_consumed_when_sole_justification", "budget_unique",
      "in_flight_flow_compat", "in_flight_override_consumed"] : List String))

#kav_check_action grantOverride invsB

-- Manual proof of the one resistant VC: `active_has_budget` under `grant_override`.
-- Same shape as `return_endorsed_pres_active_has_budget`: the granter's 5-way budget
-- debit needs an existential witness the cascade can't reconstruct; the
-- `¬ bl_exhausted` precondition pins the granter to a level with a debit target.
theorem grant_override_pres_active_has_budget
    (granter target : KAgent) (tool : KTool) (lvl : ConfLevel) (s s' : KSt)
    (hahb : active_has_budget s)
    (hg : (grantOverride granter target tool lvl).guard s)
    (hn : (grantOverride granter target tool lvl).next s s') :
    active_has_budget s' := by
  unfold active_has_budget grantOverride grant_override Kav.Action.guard Kav.Action.next at *
  intro A hactive
  have hactiveS : s.agent_active A := by
    have hfa : s'.agent_active = s.agent_active := by grind
    rw [hfa] at hactive; exact hactive
  by_cases hAg : A = granter
  · subst hAg
    obtain ⟨L, hL⟩ := hahb A hactiveS
    have hne : ¬ s.agent_budget A BudgetLevel.bl_exhausted := by grind
    have hbeq : ∀ X Y, s'.agent_budget X Y =
        ((X = A ∧
          ( (s.agent_budget A BudgetLevel.bl5 ∧ Y = BudgetLevel.bl4)
          ∨ (s.agent_budget A BudgetLevel.bl4 ∧ Y = BudgetLevel.bl3)
          ∨ (s.agent_budget A BudgetLevel.bl3 ∧ Y = BudgetLevel.bl2)
          ∨ (s.agent_budget A BudgetLevel.bl2 ∧ Y = BudgetLevel.bl1)
          ∨ (s.agent_budget A BudgetLevel.bl1 ∧ Y = BudgetLevel.bl_exhausted) ))
        ∨ (X ≠ A ∧ s.agent_budget X Y)) := by grind
    cases L with
    | bl_exhausted => exact absurd hL hne
    | bl5 => exact ⟨BudgetLevel.bl4, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hL, rfl⟩⟩⟩
    | bl4 => exact ⟨BudgetLevel.bl3, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inl ⟨hL, rfl⟩)⟩⟩
    | bl3 => exact ⟨BudgetLevel.bl2, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨hL, rfl⟩))⟩⟩
    | bl2 => exact ⟨BudgetLevel.bl1, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨hL, rfl⟩)))⟩⟩
    | bl1 => exact ⟨BudgetLevel.bl_exhausted, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨hL, rfl⟩)))⟩⟩
  · obtain ⟨L, hL⟩ := hahb A hactiveS
    refine ⟨L, ?_⟩
    have hbeq : ∀ X Y, s'.agent_budget X Y =
        ((X = granter ∧
          ( (s.agent_budget granter BudgetLevel.bl5 ∧ Y = BudgetLevel.bl4)
          ∨ (s.agent_budget granter BudgetLevel.bl4 ∧ Y = BudgetLevel.bl3)
          ∨ (s.agent_budget granter BudgetLevel.bl3 ∧ Y = BudgetLevel.bl2)
          ∨ (s.agent_budget granter BudgetLevel.bl2 ∧ Y = BudgetLevel.bl1)
          ∨ (s.agent_budget granter BudgetLevel.bl1 ∧ Y = BudgetLevel.bl_exhausted) ))
        ∨ (X ≠ granter ∧ s.agent_budget X Y)) := by grind
    rw [hbeq]; right; exact ⟨hAg, hL⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms grant_override_pres_active_has_budget

end Tzimtzum
